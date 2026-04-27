import Soma.Syntax
import Soma.Core.Module
import Soma.Core.Function
import Soma.Dependent.Monad
import Soma.Dependent.Infer
import Soma.Dependent.Unify
import Soma.Dependent.Level
import Soma.Dependent.Instance
import Soma.Dependent.Solver
import Soma.Dependent.Error
import Soma.Dependent.Totality
import Soma.Dependent.Elaborate
import Soma.Dependent.TraitElaborate
import Soma.Dependent.Zonk
import Soma.Dependent.Coverage
import Soma.Core.Eval

namespace Soma.Dependent.Driver

open Soma.Syntax
open Soma.Core (Value Level PrimOp FFIOp Intrinsic)
open Soma (UniqueSupply)

/-- Elaborate a standalone type-position expression (no outer bindings) through the unified `inferTypeExpr` path and evaluate to a Value -/
def elabTypeStandalone (ty : Soma.Syntax.Expr) : TCM Value := do
  let expr ← Soma.Dependent.inferTypeExpr ty
  TCM.evalExpr expr

/-- Sort names that `inferSyntax` resolves without needing an explicit binding -/
def isBuiltinTypeName (n : String) : Bool :=
  n == "Type" || n == "Type0" || n == "Type1" || n == "Prop"
  || n == "Row" || n == "Label"

/-- Collect every free identifier in `sigSyntax` -/
def implicitForallNames (sigSyntax : Soma.Syntax.Expr) : TCM (List String) := do
  let freeVarNames := sigSyntax.freeVars.map (·.name)
  let mut acc : Array String := #[]
  for name in freeVarNames do
    if isBuiltinTypeName name then continue
    if (← TCM.lookupGlobal #[] name).isSome then continue
    acc := acc.push name
  return acc.toList.eraseDups

/-- Elaborate a type-class method's declared signature into the canonical form -/
def elaborateTraitMethodType
    (globals : Globals) (typeClass : Soma.Core.TypeClassMeta)
    (methodTypeSyntax : Soma.Syntax.Expr) : TCM Value := do
  TCM.withGlobals globals do
    let mut traitParamNames : Array String := #[]
    let mut traitParamKindExprs : Array Soma.Core.Expr := #[]
    let mut traitParamKinds : Array Value := #[]
    for param in typeClass.params do
      traitParamNames := traitParamNames.push param.name.name
      let kindExpr ← match param.kind with
        | some k => Soma.Dependent.inferTypeExpr k
        | none => pure (.sort Level.zero)
      let kindVal ← TCM.evalExpr kindExpr
      traitParamKindExprs := traitParamKindExprs.push kindExpr
      traitParamKinds := traitParamKinds.push kindVal

    let methodFreeVars := methodTypeSyntax.freeVars.map (·.name)
    let methodOwnVars := methodFreeVars.filter (fun v => !traitParamNames.contains v)
    let methodOwnVarsUnique := methodOwnVars.toList.eraseDups
    let methodOwnVarsArr := methodOwnVarsUnique.toArray
    let M := methodOwnVarsArr.size
    let P := traitParamNames.size

    let tyTy : Value := Value.vType Level.zero

    let mut ownVarKinds : Array Value := #[]
    for _ in methodOwnVarsArr do
      ownVarKinds := ownVarKinds.push (← TCM.freshMetaVal tyTy)

    let mut ownBindings : Array (Soma.Unique × String × Value) := #[]
    for i in [:M] do
      let uid ← TCM.freshLocalId methodOwnVarsArr[i]!
      ownBindings := ownBindings.push (uid, methodOwnVarsArr[i]!, ownVarKinds[i]!)
    let mut traitBindings : Array (Soma.Unique × String × Value) := #[]
    for i in [:P] do
      let uid ← TCM.freshLocalId traitParamNames[i]!
      traitBindings := traitBindings.push (uid, traitParamNames[i]!, traitParamKinds[i]!)

    let buildInner : TCM Soma.Core.Expr := do
      let bodyExpr ← Soma.Dependent.inferTypeExpr methodTypeSyntax
      let classNameStr' := typeClass.name.display
      let ns ← TCM.getCurrentNamespace
      let ctx ← TCM.getCtx
      let instanceDomainExpr : Soma.Core.Expr :=
        match ctx.globals.resolve ns #[] classNameStr' with
        | none => .sort Level.zero
        | some classQN =>
          let argExprs : Array Soma.Core.Expr :=
            (List.range P).toArray.map (fun i => .bvar (P - 1 - i))
          .dataTy classQN.id argExprs
      pure (.pi .omega .instance_ "$dict" instanceDomainExpr bodyExpr.shiftUp)

    let ownWrapped ← ownBindings.foldrM (init := do
      traitBindings.foldrM (init := buildInner)
        (fun (uid, name, kind) acc =>
          pure (TCM.withBinding name uid kind .omega .implicit Span.uninhabited acc)))
      (fun (uid, name, kind) acc =>
        pure (TCM.withBinding name uid kind .omega .implicit Span.uninhabited acc))
    let innerInner ← ownWrapped
    let innerBody ← innerInner

    let mut piExpr : Soma.Core.Expr := innerBody
    for i in [:P] do
      let idx := P - 1 - i
      let name := traitParamNames[idx]!
      let kindExpr := traitParamKindExprs[idx]!
      piExpr := .pi .omega .implicit name kindExpr piExpr
    for i in [:M] do
      let idx := M - 1 - i
      let name := methodOwnVarsArr[idx]!
      let kindExpr := Soma.Core.quoteExpr0 (← zonkValue ownVarKinds[idx]!)
      piExpr := .pi .omega .implicit name kindExpr piExpr
    TCM.evalExprInEnv Soma.Core.Env.empty piExpr


/-- Convert TCError to Diagnostic -/
def tcErrorToDiagnostic (e : TCError) : Diagnostic :=
  e.toDiagnostic

/-- Convert array of TCErrors to Diagnostics -/
def tcErrorsToDiagnostics (errors : Array TCError) : Diagnostics :=
  errors.map tcErrorToDiagnostic

/-- State maintained across function checks for totality tracking -/
structure CheckState where
  /-- Registry of function totality status -/
  registry : Totality.TotalityRegistry := Totality.TotalityRegistry.empty
  /-- Accumulated errors -/
  errors : Array TCError := #[]

private def inferIntrinsicInfo (fn : Soma.Core.UntypedFunction) : TCM (Option Intrinsic) :=
  match fn.attrs.intrinsic with
  | some tag =>
    if tag.isEmpty then
      TCM.throw (.cannotInfer
        s!"@[intrinsic] on '{fn.name.display}' requires a tag string, e.g. @[intrinsic \"primop.add\"]"
        fn.span none)
    else
      match Intrinsic.fromTag? tag with
      | some i => pure (some i)
      | none => TCM.throw (.cannotInfer
          s!"unknown intrinsic tag '{tag}' on '{fn.name.display}'"
          fn.span none)
  | none =>
    pure (fn.attrs.extern.map Intrinsic.extern)

/-- Check totality for a function if it's marked @[total] -/
def checkFunctionTotality (fn : Soma.Core.UntypedFunction) (body : Soma.Core.Expr)
    (registry : Totality.TotalityRegistry) : Totality.TotalityRegistry × Array TCError :=
  let fnInfo : Totality.FunctionInfo := {
    name := fn.name
    markedTotal := fn.attrs.total
    status := .isUnknown
    params := fn.params
    fnType := Value.vType .zero
    span := fn.span
  }
  let (registry', result) := Totality.checkAndRegisterTotality fnInfo body registry
  (registry', result.errors)

/-- Extract explicit parameter types from a Pi type, returning (paramTypes, resultType) -/
partial def extractParamTypes (ty : Value) (numParams : Nat) : TCM (Array Value × Value) := do
  if numParams == 0 then
    return (#[], ty)
  else
    let ty' ← force ty
    match ty' with
    | .vPi _qty binder _name dom cod =>
      -- Get the codomain by applying the closure to a dummy value
      let lvl ← TCM.currentLevel
      let dummyArg := Value.vNeutral dom (.nVar ⟨"_", lvl⟩)
      let codTy ← applyClosure cod dummyArg
      if binder.isImplicit then
        -- Skip implicit parameters since they get instantiated with metavariables
        extractParamTypes codTy numParams
      else
        -- Explicit parameter, include in the result
        let (restParams, resultTy) ← extractParamTypes codTy (numParams - 1)
        return (#[dom] ++ restParams, resultTy)
    | _ =>
      -- Not a Pi type, return remaining as result
      return (#[], ty')

/-- Extract a binder telescope prefix from a Pi type, preserving QTT quantities -/
partial def extractSignaturePrefix (ty : Value) (numExplicit : Nat)
    : TCM (Array (String × Value × Soma.Core.BinderInfo × Soma.Core.Quantity) × Value) := do
  let startLvl ← TCM.currentLevel
  go ty numExplicit startLvl.lvl
where
  go (ty : Value) (numExplicit : Nat) (lvl : Nat)
      : TCM (Array (String × Value × Soma.Core.BinderInfo × Soma.Core.Quantity) × Value) := do
    let ty' ← force ty
    match ty' with
    | .vPi qty binder name dom cod =>
      if numExplicit == 0 && !binder.isImplicit then
        return (#[], ty')
      let dummyArg := Value.vNeutral dom (.nVar ⟨name, ⟨lvl⟩⟩)
      let codTy ← applyClosure cod dummyArg
      let remainingExplicit := if binder.isImplicit then numExplicit else numExplicit - 1
      let (restParams, resultTy) ← go codTy remainingExplicit (lvl + 1)
      return (#[(name, dom, binder, qty)] ++ restParams, resultTy)
    | _ =>
      return (#[], ty')

/-- Extend the context with function parameters and run an action -/
def withFunctionParams (params : Array String) (paramTypes : Array Value)
    (span : Span) (action : TCM α) : TCM (Array (Soma.Unique × String) × α) := do
  -- First generate all local ids
  let mut bindings : Array (Soma.Unique × String) := #[]
  for name in params do
    let bindingId ← TCM.freshLocalId name
    bindings := bindings.push (bindingId, name)
  -- Then extend context with each
  let rec go (idx : Nat) : TCM α := do
    if idx >= bindings.size then
      action
    else
      let (bindingId, name) := bindings[idx]!
      let paramTy := if h : idx < paramTypes.size then paramTypes[idx] else Value.vType .zero
      TCM.withBinding name bindingId paramTy .omega .explicit span do
        go (idx + 1)
  let result ← go 0
  return (bindings, result)

/-- Extend the context with a signature telescope prefix, then run an action.
  Explicit binders in the prefix are renamed to the concrete function parameter names.
  QTT quantities from the type signature are preserved in the binding context.
  Returns generated Unique×String pairs for those explicit term parameters. -/
def withSignaturePrefixBindings (allParams : Array (String × Value × Soma.Core.BinderInfo × Soma.Core.Quantity))
    (explicitParams : Array String)
    (span : Span) (action : TCM α) : TCM (Array (Soma.Unique × String) × α) := do
  -- Pre-generate all local ids to collect them
  let mut explicitBindings : Array (Soma.Unique × String) := #[]
  let mut allBindings : Array (Soma.Unique × String × Soma.Core.BinderInfo × Soma.Core.Quantity) := #[]
  let mut eIdx : Nat := 0
  for (name, _, binder, qty) in allParams do
    if binder.isImplicit then
      let bindingId ← TCM.freshLocalId name
      allBindings := allBindings.push (bindingId, name, binder, qty)
    else
      let paramName := if h : eIdx < explicitParams.size then explicitParams[eIdx] else name
      let bindingId ← TCM.freshLocalId paramName
      allBindings := allBindings.push (bindingId, paramName, .explicit, qty)
      explicitBindings := explicitBindings.push (bindingId, paramName)
      eIdx := eIdx + 1
  -- Now bind them all, using the quantity from the type signature
  let rec go (idx : Nat) : TCM α := do
    if idx >= allBindings.size then
      action
    else
      let (bindingId, paramName, binder, qty) := allBindings[idx]!
      let (_, ty, _, _) := allParams[idx]!
      withCheckedBinding paramName bindingId ty qty binder span do
        go (idx + 1)
  let result ← go 0
  return (explicitBindings, result)

/-- Elaborate a function type signature -/
def elaborateFunctionType (sigSyntax : Syntax.Expr) : TCM Value := do
  let freeVarNamesUnique ← implicitForallNames sigSyntax

  let tyTy : Value := Value.vType Level.zero
  let N := freeVarNamesUnique.length

  let mut bindingIds : Array (Soma.Unique × String) := #[]
  for varName in freeVarNamesUnique do
    let uid ← TCM.freshLocalId varName
    bindingIds := bindingIds.push (uid, varName)

  let go : TCM Soma.Core.Expr := do
    let bodyExpr ← Soma.Dependent.inferTypeExpr sigSyntax
    let bodyVal ← TCM.evalExpr bodyExpr
    pure (Soma.Core.quoteExpr ⟨N⟩ bodyVal)
  let wrapped ← bindingIds.foldrM (init := go)
    (fun (uid, name) acc => pure (TCM.withBinding name uid tyTy .omega .implicit Span.uninhabited acc))
  let closedBodyExpr ← wrapped

  let mut piExpr : Soma.Core.Expr := closedBodyExpr
  for i in [:N] do
    let idx := N - 1 - i
    let name := freeVarNamesUnique[idx]!
    piExpr := Soma.Core.Expr.pi .omega .implicit name (.sort Level.zero) piExpr
  let fnType ← TCM.evalExprInEnv Soma.Core.Env.empty piExpr

  let _ ← Soma.Dependent.solveConstraintsSilently
  return fnType

/-- Finds the index among explicit binders of the first pi whose domain is uninhabited per `Coverage.liveCandidates` -/
partial def findFirstUninhabitedExplicit (ty : Value) : TCM (Option Nat) := do
  let rec go (ty : Value) (explicitIdx : Nat) : TCM (Option Nat) := do
    let ty' ← force ty
    match ty' with
    | .vPi _ binder name dom cod =>
      if binder.isImplicit then
        let lvl ← TCM.currentLevel
        let dummy := Value.vNeutral dom (.nVar ⟨name, lvl⟩)
        let codTy ← applyClosure cod dummy
        go codTy explicitIdx
      else
        let savedState ← get
        let (isOpen, cands) ← Coverage.liveCandidates dom
        set savedState
        if !isOpen ∧ cands.isEmpty then
          return some explicitIdx
        let lvl ← TCM.currentLevel
        let dummy := Value.vNeutral dom (.nVar ⟨name, lvl⟩)
        let codTy ← applyClosure cod dummy
        go codTy (explicitIdx + 1)
    | _ => return none
  go ty 0

/-- Synthesise the AST body for a bodiless ex-falso -/
def synthesizeExFalsoBody (k : Nat) (span : Span) : Soma.Syntax.Expr :=
  let names : Array String := (Array.range (k + 1)).map (fun i => s!"_arg{i}")
  let lambdaParams : Array (Soma.Syntax.QualName × Option Soma.Syntax.Expr) :=
    names.map fun n => (⟨#[], n, span⟩, none)
  let scrutName := names.back!
  let scrutinee := Soma.Syntax.Expr.var ⟨#[], scrutName, span⟩
  let emptyMatch := Soma.Syntax.Expr.case #[scrutinee] #[] span
  Soma.Syntax.Expr.lambda lambdaParams emptyMatch span

/-- Type check a single function returning the elaborated type, body, param ids, and whether errored -/
def checkFunction (fn : Soma.Core.UntypedFunction)
  : TCM (Value × Soma.Core.Expr × Array (Soma.Unique × String) × Bool) := do
  let span := fn.span
  let storedType : Option Value ← match ← TCM.lookupGlobalByQN fn.name with
    | some info => pure (some info.type)
    | none => pure none
  if fn.attrs.intrinsic.isSome || fn.attrs.extern.isSome then
    match fn.declaredTypeSyntax with
    | some _ =>
      let declaredType ← match storedType with
        | some ty => pure ty
        | none => TCM.freshMetaVal (.vType .zero)
      Soma.Dependent.drainConstraints
      let declaredType' ← zonkValue declaredType
      reportUnsolvedMetas declaredType' span
      let declaredType'' ← expandAbbrevValue declaredType'
      return (declaredType'', Soma.Core.TypedFunction.externBody fn.name, #[], false)
    | none =>
      let ty ← TCM.freshMetaVal (.vType .zero)
      return (ty, Soma.Core.TypedFunction.externBody fn.name, #[], false)
  match fn.declaredTypeSyntax with
  | some typeSyntax =>
    let declaredType ← match storedType with
      | some ty => pure ty
      | none =>
        TCM.recoverWithM
          (elaborateFunctionType typeSyntax)
          (TCM.typePlaceholder span)
    -- Split declared signature into:
    --   1) telescope prefix needed to check this function's term parameters
    --   2) remaining result type outside that prefix
    let (allParams, resultType) ← TCM.recoverWith
      (extractSignaturePrefix declaredType fn.params.size)
      (#[], declaredType)
    let explicitInSig := allParams.filter (fun (_, _, binder, _) => !binder.isImplicit) |>.size
    if explicitInSig ≥ 1 ∧ explicitInSig < fn.params.size then
      let resolvedResult ← TCM.recoverWith (zonkValue resultType >>= expandAbbrevValue) resultType
      TCM.addError
        (.patternArityMismatch fn.name.display explicitInSig fn.params.size resolvedResult span)
      let declaredType' ← zonkValue declaredType
      let declaredType'' ← expandAbbrevValue declaredType'
      return (declaredType'', Soma.Core.TypedFunction.erroredBody fn.name, #[], true)
    let effectiveBody : Option Soma.Syntax.Expr ←
      if fn.isBodilessExFalso then
        match ← findFirstUninhabitedExplicit resultType with
        | some k => pure (some (synthesizeExFalsoBody k span))
        | none   => pure none
      else pure (some fn.body)
    match effectiveBody with
    | none =>
      Soma.Dependent.drainConstraints
      let declaredType' ← zonkValue declaredType
      reportUnsolvedMetas declaredType' span
      let resolved' ← expandAbbrevValue declaredType'
      TCM.addError (.bodilessNotDerivable fn.name.display resolved' span)
      return (resolved', Soma.Core.TypedFunction.erroredBody fn.name, #[], true)
    | some body =>
      let bodyIsProof ← Soma.Dependent.valueInPropUniverse resultType
      let runBodyCheck : TCM Soma.Core.Expr :=
        TCM.infallible (Soma.Dependent.checkSyntax body resultType) default
      let (generatedParams, typedBody) ← withSignaturePrefixBindings allParams fn.params span do
        if bodyIsProof then TCM.inErasedContext runBodyCheck else runBodyCheck
      Soma.Dependent.drainConstraints
      let declaredType' ← zonkValue declaredType
      reportUnsolvedMetas declaredType' span
      let typedBody' ← zonkExpr typedBody
      Soma.Dependent.zonkLocalTypesInPlace
      let declaredType'' ← expandAbbrevValue declaredType'
      return (declaredType'', typedBody', generatedParams, false)
  | none =>
    -- No signature: create fresh metavariables for param types
    let paramTypes ← fn.params.mapM fun _ => TCM.freshMetaVal (.vType .zero)
    -- Extend context with parameters and infer body type
    let (generatedParams, (inferredType, typedBody)) ← withFunctionParams fn.params paramTypes span do
      TCM.infallibleExpr (Soma.Dependent.inferSyntax fn.body) span
    -- Solve pending instance constraints before zonking
    Soma.Dependent.drainConstraints
    -- Zonk all solved metas so downstream passes see concrete types
    let inferredType' ← zonkValue inferredType
    reportUnsolvedMetas inferredType' span
    let typedBody' ← zonkExpr typedBody
    Soma.Dependent.zonkLocalTypesInPlace
    -- Expand parameterized type abbreviations so downstream passes see real types
    let inferredType'' ← expandAbbrevValue inferredType'
    return (inferredType'', typedBody', generatedParams, false)

/-- Elaborate a constructor type -/
def elaborateCtorType (typeName : Soma.Core.QualifiedName)
    (typeVarBinders : Array Syntax.TypeVarBinder)
    (fieldTypeSyntax : Array Syntax.Expr) : TCM Value := do
  let N := typeVarBinders.size

  let mut paramKindExprs : Array Soma.Core.Expr := #[]
  let mut paramKinds : Array Value := #[]
  for binder in typeVarBinders do
    let kindExpr ← match binder.kind with
      | some k => Soma.Dependent.inferTypeExpr k
      | none => pure (.sort Level.zero)
    let kindVal ← TCM.evalExpr kindExpr
    paramKindExprs := paramKindExprs.push kindExpr
    paramKinds := paramKinds.push kindVal

  let mut bindings : Array (Soma.Unique × String) := #[]
  for binder in typeVarBinders do
    let uid ← TCM.freshLocalId binder.name.name
    bindings := bindings.push (uid, binder.name.name)

  let buildInner : TCM Soma.Core.Expr := do
    let mut typeVarVals : List Value := []
    for (_, name) in bindings do
      match ← TCM.lookupLocal name with
      | some entry =>
        typeVarVals := typeVarVals ++
          [Value.vNeutral entry.type (Soma.Core.Neutral.nVar ⟨name, entry.level⟩)]
      | none => pure ()
    let mut ctorVal : Value := Value.vDataType typeName.id typeVarVals
    for fieldTy in fieldTypeSyntax.reverse do
      let fieldExpr ← Soma.Dependent.inferTypeExpr fieldTy
      let fieldVal ← TCM.evalExpr fieldExpr
      ctorVal := Value.vPi .omega .explicit "_" fieldVal (Soma.Core.Closure.const "_" ctorVal)
    pure (Soma.Core.quoteExpr ⟨N⟩ ctorVal)

  let wrapped ← bindings.zip paramKinds |>.foldrM (init := buildInner)
    (fun ((uid, name), kindVal) acc =>
      pure (TCM.withBinding name uid kindVal .omega .implicit Span.uninhabited acc))
  let innerBody ← wrapped

  let mut piExpr : Soma.Core.Expr := innerBody
  for i in [:N] do
    let idx := N - 1 - i
    let name := typeVarBinders[idx]!.name.name
    let kindExpr := paramKindExprs[idx]!
    piExpr := .pi .omega .implicit name kindExpr piExpr
  TCM.evalExprInEnv Soma.Core.Env.empty piExpr

/-- Elaborate an indexed constructor type from a full user-written signature -/
def elaborateIndexedCtorType (_typeName : Soma.Core.QualifiedName)
    (_typeVarNames : Array String) (sigSyntax : Syntax.Expr) : TCM Value := do
  let freeVarNamesUnique ← implicitForallNames sigSyntax

  let tyTy : Value := Value.vType Level.zero
  let N := freeVarNamesUnique.length

  let mut bindings : Array (Soma.Unique × String × Value) := #[]
  for varName in freeVarNamesUnique do
    let uid ← TCM.freshLocalId varName
    let kindMeta ← TCM.freshMetaVal tyTy
    bindings := bindings.push (uid, varName, kindMeta)

  let buildInner : TCM Soma.Core.Expr := do
    let bodyExpr ← Soma.Dependent.inferTypeExpr sigSyntax
    let bodyVal ← TCM.evalExpr bodyExpr
    pure (Soma.Core.quoteExpr ⟨N⟩ bodyVal)

  let wrapped ← bindings.foldrM (init := buildInner)
    (fun (uid, name, kind) acc =>
      pure (TCM.withBinding name uid kind .omega .implicit Span.uninhabited acc))
  let innerBody ← wrapped

  let mut piExpr : Soma.Core.Expr := innerBody
  for i in [:N] do
    let idx := N - 1 - i
    let name := freeVarNamesUnique[idx]!
    let (_, _, kindVal) := bindings[idx]!
    let kindExpr ← do
      let zonked ← zonkValue kindVal
      pure (Soma.Core.quoteExpr0 zonked)
    piExpr := .pi .omega .implicit name kindExpr piExpr
  TCM.evalExprInEnv Soma.Core.Env.empty piExpr

private def registerWiredRoleFromAttrs
    (globals : Globals)
    (attrs : Array Syntax.Attribute)
    (info : GlobalInfo)
    (what : String)
    : TCM Globals := do
  let mut g := globals
  for attr in attrs do
    if attr.name.name == "wired_in" then
      match attr.args[0]? with
      | some (Soma.Syntax.Expr.lit (Soma.Syntax.Literal.string roleName _)) =>
        match WiredRole.fromString? roleName with
        | none =>
          TCM.throw (.cannotInfer s!"unknown wired_in role '{roleName}' on {what}" attr.span none)
        | some role =>
          let existing := g.wiredIn.getAll role
          let conflicts := existing.filter (fun e => e.name != info.name)
          if conflicts.isEmpty then
            g := { g with wiredIn := g.wiredIn.register role info }
          else
            let prev := String.intercalate ", " ((conflicts.map (fun e => e.name.display)).toList)
            TCM.throw (.cannotInfer s!"duplicate wired_in role '{role.canonical}' on {what}; already bound to {prev}" attr.span none)
      | _ =>
        TCM.throw (.cannotInfer s!"@[wired_in] on {what} requires a string literal role argument" attr.span none)
  pure g

private def indexWiredRoles (module : Soma.Core.UntypedModule) (globals : Globals) : TCM Globals := do
  let mut g := globals
  for typeDef in module.types do
    match typeDef with
    | .algebraic attrs typeName _ ctors _ _ =>
      if let some typeInfo := g.getDef typeName then
        g ← registerWiredRoleFromAttrs g attrs typeInfo s!"type {typeName.display}"
      for ctor in ctors do
        if let some ctorInfo := g.getDef ctor.name then
          g ← registerWiredRoleFromAttrs g ctor.attrs ctorInfo s!"constructor {ctor.name.display}"
    | .record attrs recordName _ _ _ _ =>
      if let some typeInfo := g.getDef recordName then
        g ← registerWiredRoleFromAttrs g attrs typeInfo s!"type {recordName.display}"
  for fn in module.functions do
    if let some roleName := fn.attrs.wiredIn then
      if let some fnInfo := g.getDef fn.name then
        match WiredRole.fromString? roleName with
        | some role =>
          let existing := g.wiredIn.getAll role
          let conflicts := existing.filter (fun e => e.name != fnInfo.name)
          if conflicts.isEmpty then
            g := { g with wiredIn := g.wiredIn.register role fnInfo }
          else
            let prev := String.intercalate ", " ((conflicts.map (fun e => e.name.display)).toList)
            TCM.throw (.cannotInfer s!"duplicate wired_in role '{role.canonical}' on function {fn.name.display}; already bound to {prev}" fn.span none)
        | none =>
          TCM.throw (.cannotInfer s!"unknown wired_in role '{roleName}' on function {fn.name.display}" fn.span none)
  pure g

/-- Elaborate the type constructor kind for a type class head -/
private def elaborateTypeClassHeadType
    (typeClass : Soma.Core.TypeClassMeta)
    : TCM Value := do
  let mut paramKinds : Array (String × Value) := #[]
  for param in typeClass.params do
    let kind ← match param.kind with
      | some k => elabTypeStandalone k
      | none => pure (Value.vType Level.zero)
    paramKinds := paramKinds.push (param.name.name, kind)

  let mut classHeadTy : Value := Value.vType Level.zero
  for (paramName, paramKind) in paramKinds.reverse do
    classHeadTy := Value.vPi .omega .explicit paramName paramKind
      (Soma.Core.Closure.const paramName classHeadTy)
  return classHeadTy

/-- Register or reuse a type class head symbol as a global type -/
private def registerTypeClassHead
    (globals : Globals)
    (typeClass : Soma.Core.TypeClassMeta)
    (prevGlobals : Option Globals)
    (isDirty : Bool)
    : TCM Globals := do
  let classNameStr := typeClass.name.display

  let ns ← TCM.getCurrentNamespace

  if !isDirty then
    if let some prev := prevGlobals then
      if let some info := prev.getDef typeClass.name then
        return globals.register ns classNameStr info

  let classQN := typeClass.name

  let mut g := globals

  let classHeadTy ← TCM.recoverWithM
    (TCM.withGlobals g (elaborateTypeClassHeadType typeClass))
    (TCM.typePlaceholder typeClass.span)

  let classInfo : GlobalInfo := {
    name := classQN
    type := classHeadTy
    value := some (Value.vDataType classQN.id [])
    isConstructor := false
    origin := .class_
  }
  g := g.register ns classNameStr classInfo
  return g

/-- Build the eta-expanded Value for a constructor -/
partial def mkConstructorValue
    (qn : Soma.Core.QualifiedName) (tag : Nat)
    (ctorType : Soma.Core.Value) : Soma.Core.Value := Id.run do
  let (binders, explicitLevels, rty) := collectCtorPis ctorType 0 #[] #[]
  let N := binders.size
  let rtyE := Soma.Core.quoteExpr ⟨N⟩ rty
  let explicitBvars : Array Soma.Core.Expr :=
    explicitLevels.map (fun lvl => Soma.Core.Expr.bvar (N - 1 - lvl))
  let mut body : Soma.Core.Expr := .construct qn tag explicitBvars rtyE
  for i in [:N] do
    let idx := N - 1 - i
    let (binder, name, domE) := binders[idx]!
    body := .lam binder name domE body
  return Soma.Core.evalClosed body
where
  collectCtorPis (ty : Soma.Core.Value) (depth : Nat)
      (binders : Array (Soma.Core.BinderInfo × String × Soma.Core.Expr))
      (explicitLevels : Array Nat)
      : Array (Soma.Core.BinderInfo × String × Soma.Core.Expr) × Array Nat × Soma.Core.Value :=
    match ty with
    | .vPi _qty binder name dom cod =>
      let domE := Soma.Core.quoteExpr ⟨depth⟩ dom
      let binders' := binders.push (binder, name, domE)
      let explicit' :=
        if binder.isImplicit then explicitLevels else explicitLevels.push depth
      let freshVal := Soma.Core.Value.vNeutral dom (Soma.Core.Neutral.nVar ⟨name, ⟨depth⟩⟩)
      let nextTy := cod.applyPure freshVal
      collectCtorPis nextTy (depth + 1) binders' explicit'
    | _ => (binders, explicitLevels, ty)

/-- Elaborate a type constructor's head kind from its parameter binders -/
def elaborateTypeHeadKind
    (binders : Array Syntax.TypeVarBinder)
    (resultSort : Soma.Core.Level := Level.zero) : TCM Value := do
  let mut paramKinds : Array (String × Value × Soma.Core.Quantity) := #[]
  for binder in binders do
    let kind ← match binder.kind with
      | some k => elabTypeStandalone k
      | none => pure (Value.vType Level.zero)
    -- A data-type parameter whose kind is an universe or Prop-valued gets quantity 0
    let qty ← if (← Soma.Dependent.shouldAutoEraseBinder kind) then pure .zero else pure .omega
    paramKinds := paramKinds.push (binder.name.name, kind, qty)
  let mut headKind : Value := Value.vType resultSort
  for (paramName, paramKind, qty) in paramKinds.reverse do
    headKind := Value.vPi qty .explicit paramName paramKind
      (Soma.Core.Closure.const paramName headKind)
  return headKind

/-- Pre-register all type names from a module -/
def preRegisterTypes (module : Soma.Core.UntypedModule) : TCM Globals := do
  let ctx ← TCM.getCtx
  let ns := ctx.currentNamespace
  let mut globals := ctx.globals
  for typeDef in module.types do
    match typeDef with
    | .algebraic _ typeName binders _ headSort _ =>
      let typeQN := typeName
      let headKind ← TCM.withGlobals globals (elaborateTypeHeadKind binders headSort)
      globals := globals.registerInductive typeQN .algebraic
        (binders.map (·.name.name)) #[] headSort
      let dataTypeInfo : GlobalInfo := {
        name := typeQN
        type := headKind
        value := some (Value.vDataType typeQN.id [])
        isConstructor := false
        origin := .typeDecl
      }
      globals := globals.register ns typeName.display dataTypeInfo
    | .record _ recordName binders _ fields _ =>
      let typeQN := recordName
      let headKind ← TCM.withGlobals globals (elaborateTypeHeadKind binders)
      globals := globals.registerInductive typeQN .record
        (binders.map (·.name.name))
        (fields.filterMap (·.1))
      let dataTypeInfo : GlobalInfo := {
        name := typeQN
        type := headKind
        value := some (Value.vDataType typeQN.id [])
        isConstructor := false
        origin := .typeDecl
      }
      globals := globals.register ns recordName.display dataTypeInfo
  return globals

/-- After `buildInstanceEnv`, drain any instance-resolution constraints left and zonk metas -/
def resolveAndZonkSignatures (module : Soma.Core.UntypedModule) : TCM Globals := do
  let ctx ← TCM.getCtx
  let ns := ctx.currentNamespace
  Soma.Dependent.drainConstraints
  let mut globals := ctx.globals
  for fn in module.functions ++ module.theorems do
    if fn.declaredTypeSyntax.isNone then continue
    match globals.getDef fn.name with
    | none => pure ()
    | some info =>
      let zonked ← zonkValue info.type
      let expanded ← expandAbbrevValue zonked
      let info' := { info with type := expanded }
      globals := { globals with defs := globals.defs.insert fn.name info' }
      globals := globals.register ns fn.name.display info'
  return globals

/-- Build the InstanceEnv from module type classes and instances -/
def buildInstanceEnv (module : Soma.Core.UntypedModule) (_moduleName : String)
    : TCM (InstanceEnv × TraitElaborate.InstanceMap × Array Soma.Core.TypedFunction
          × Array TraitElaborate.PendingInstanceBodies) := do
  TraitElaborate.buildInstanceEnvFromModule module

/-- Build the InstanceEnv incrementally, reusing cached info for unchanged definitions -/
def buildInstanceEnvIncremental
  (module : Soma.Core.UntypedModule)
    (_moduleName : String)
    (prevEnv : InstanceEnv)
    (prevInstanceMap : TraitElaborate.InstanceMap)
    (dirtyNames : Std.HashSet String)
    : TCM (InstanceEnv × TraitElaborate.InstanceMap × Array Soma.Core.TypedFunction
          × Array TraitElaborate.PendingInstanceBodies) := do
  TraitElaborate.buildInstanceEnvFromModuleIncremental module prevEnv prevInstanceMap dirtyNames

/-- Run body elaboration for every pending instance from `buildInstanceEnv` -/
def runPendingInstanceBodies
    (pending : Array TraitElaborate.PendingInstanceBodies)
    : TCM (Array Soma.Core.TypedFunction) := do
  TraitElaborate.runAllPendingInstanceBodies pending

/-- Elaborate a single type abbreviation into an AbbrevInfo.

    For non-parameterized abbreviations like `abbrev CInt = Int32`:
      - Directly elaborates the expansion to a Value

    For parameterized abbreviations like `abbrev MyList a = List a`:
      - Creates an elaboration environment with the type parameters
      - Elaborates the expansion in that environment
      - Wraps the result in Pi types (right to left) -/
def elaborateAbbrev (typeAbbrev : Soma.Core.TypeAbbrev) : TCM AbbrevInfo := do
  let abbrevUnique ← TCM.freshUnique typeAbbrev.name
  let arity := typeAbbrev.params.size

  if typeAbbrev.params.isEmpty then
    -- Non-parameterized: elaborate expansion directly
    let expansion ← elabTypeStandalone typeAbbrev.expansion
    return { abbrevId := abbrevUnique, arity := 0, expansion, span := typeAbbrev.span }
  else
    let tyTy : Value := Value.vType Level.zero
    let N := typeAbbrev.params.size

    let mut bindings : Array (Soma.Unique × String) := #[]
    for paramName in typeAbbrev.params do
      let uid ← TCM.freshLocalId paramName
      bindings := bindings.push (uid, paramName)

    let buildInner : TCM Soma.Core.Expr := do
      let expr ← Soma.Dependent.inferTypeExpr typeAbbrev.expansion
      let bodyVal ← TCM.evalExpr expr
      pure (Soma.Core.quoteExpr ⟨N⟩ bodyVal)

    let wrapped ← bindings.foldrM (init := buildInner)
      (fun (uid, name) acc =>
        pure (TCM.withBinding name uid tyTy .omega .explicit Span.uninhabited acc))
    let innerExpr ← wrapped

    let mut piExpr : Soma.Core.Expr := innerExpr
    for i in [:N] do
      let idx := N - 1 - i
      let name := typeAbbrev.params[idx]!
      piExpr := .lam .explicit name (.sort Level.zero) piExpr

    let expansion ← TCM.evalExprInEnv Soma.Core.Env.empty piExpr
    return { abbrevId := abbrevUnique, arity, expansion, span := typeAbbrev.span }

/-- Build the AbbrevEnv from module type abbreviations -/
def buildAbbrevEnv (module : Soma.Core.UntypedModule) : TCM AbbrevEnv := do
  let mut env : AbbrevEnv := {}
  for typeAbbrev in module.abbreviations do
    let info ← elaborateAbbrev typeAbbrev
    env := env.insert ⟨info.abbrevId⟩ info
  return env

/-- Register or reuse a data type definition, returns updated globals -/
private def registerDataType
    (globals : Globals)
    (typeQN : Soma.Core.QualifiedName)
    (kind : InductiveKind)
    (binders : Array Syntax.TypeVarBinder := #[])
    (fieldNames : Array String := #[])
    (headSort : Soma.Core.Level := Soma.Core.Level.zero)
    (prevGlobals : Option Globals)
    (isDirty : Bool)
    : TCM Globals := do
  let ns ← TCM.getCurrentNamespace
  let nameStr := typeQN.display
  let typeVarNames := binders.map (·.name.name)
  if !isDirty then
    if let some prev := prevGlobals then
      if let some prevQN := prev.resolve ns #[] nameStr then
        if let some info := prev.getDef prevQN then
          let mut g := globals.register ns nameStr info
          g := g.registerInductive prevQN kind typeVarNames fieldNames
          return g

  let headKind ← TCM.withGlobals globals (elaborateTypeHeadKind binders headSort)
  let mut g := globals.registerInductive typeQN kind typeVarNames fieldNames headSort
  let dataTypeInfo : GlobalInfo := {
    name := typeQN
    type := headKind
    value := some (Value.vDataType typeQN.id [])
    isConstructor := false
    origin := .typeDecl
  }
  return g.register ns nameStr dataTypeInfo

/-- Core constructor registration logic -/
private def registerConstructorRaw
    (globals : Globals)
    (typeName : Soma.Core.QualifiedName)
    (typeVarBinders : Array Syntax.TypeVarBinder)
    (ctorQN : Soma.Core.QualifiedName)
    (ctorSimpleName : String)
    (ctorTag : Nat)
    (fieldTypes : Array Syntax.Expr)
    (sigSyntax : Option Syntax.Expr)
    (prevGlobals : Option Globals)
    (isDirty : Bool)
    : TCM Globals := do
  let ns ← TCM.getCurrentNamespace
  let typeNs := ns.push typeName.display
  let typeVarNames := typeVarBinders.map (·.name.name)

  if !isDirty then
    if let some prev := prevGlobals then
      if let some prevCtorQN := prev.resolve ns #[typeName.display] ctorSimpleName then
        if let some info := prev.getDef prevCtorQN then
          let mut g := globals.register typeNs ctorSimpleName info
          g := g.registerConstructorMeta typeName {
            name := info.name
            simpleName := ctorSimpleName
            tag := info.ctorTag
            arity := info.type.explicitArityFull
            type := info.type
          }
          return g

  let ctorType ← TCM.recoverWithM
    (match sigSyntax with
      | some sig => TCM.withGlobals globals (elaborateIndexedCtorType typeName typeVarNames sig)
      | none => TCM.withGlobals globals (elaborateCtorType typeName typeVarBinders fieldTypes))
    (TCM.typePlaceholder Span.uninhabited)
  let ctorValue := mkConstructorValue ctorQN ctorTag ctorType
  let info : GlobalInfo := {
    name := ctorQN
    type := ctorType
    value := some ctorValue
    isConstructor := true
    ctorTag := ctorTag
    origin := .constructor
  }
  let mut g := globals.register typeNs ctorSimpleName info
  g := g.registerConstructorMeta typeName {
    name := info.name
    simpleName := ctorSimpleName
    tag := ctorTag
    arity := fieldTypes.size
    type := ctorType
  }
  return g

/-- Register or reuse a constructor from an `UntypedConstructor` record -/
private def registerConstructor
    (globals : Globals)
  (typeName : Soma.Core.QualifiedName)
    (typeVarBinders : Array Syntax.TypeVarBinder)
  (ctor : Soma.Core.UntypedConstructor)
    (prevGlobals : Option Globals)
    (isDirty : Bool)
    : TCM Globals :=
  registerConstructorRaw globals typeName typeVarBinders
    ctor.name ctor.name.id.original ctor.tag ctor.fieldTypeSyntax ctor.sigSyntax
    prevGlobals isDirty

/-- Register or reuse record field accessors, returns updated globals -/
private def registerRecordFieldAccessors
    (globals : Globals)
    (recordName : Soma.Core.QualifiedName)
    (fields : Array (Option String × Syntax.Expr))
    (prevGlobals : Option Globals)
    (isDirty : Bool)
    : TCM Globals := do
  let ns ← TCM.getCurrentNamespace
  let typeNs := ns.push recordName.display
  let mut g := globals

  if !isDirty then
    if let some prev := prevGlobals then
      for (fieldNameOpt, _) in fields do
        if let some fieldName := fieldNameOpt then
          if let some accQN := prev.resolve ns #[recordName.display] fieldName then
            if let some accessorInfo := prev.getDef accQN then
              g := g.register typeNs fieldName accessorInfo
      return g

  for (fieldNameOpt, _) in fields do
    if let some fieldName := fieldNameOpt then
      let accessorUnique ← TCM.freshUnique fieldName
      let accessorType ← TCM.freshMetaVal (.vType .zero)
      let accessorInfo : GlobalInfo := {
        name := ⟨accessorUnique⟩
        type := accessorType
        value := none
        isConstructor := false
        origin := .projection
      }
      g := g.register typeNs fieldName accessorInfo
  return g

/-- Register or reuse a record constructor and its field accessors, returns updated globals -/
private def registerRecordConstructor
    (globals : Globals)
    (recordName : Soma.Core.QualifiedName)
    (typeVarBinders : Array Syntax.TypeVarBinder)
    (ctorName : Soma.Core.QualifiedName)
    (fields : Array (Option String × Syntax.Expr))
    (prevGlobals : Option Globals)
    (isDirty : Bool)
    : TCM Globals := do
  let g ← registerConstructorRaw globals recordName typeVarBinders
    ctorName "New" 0 (fields.map (·.2)) none prevGlobals isDirty
  registerRecordFieldAccessors g recordName fields prevGlobals isDirty

/-- Elaborate a type class method type -/
private def elaborateMethodType
    (globals : Globals)
    (typeClass : Soma.Core.TypeClassMeta)
    (methodTypeSyntax : Syntax.Expr)
    : TCM Value :=
  elaborateTraitMethodType globals typeClass methodTypeSyntax

/-- Register or reuse a type class method, returns updated globals -/
private def registerMethod
    (globals : Globals)
  (typeClass : Soma.Core.TypeClassMeta)
  (methodName : Soma.Core.QualifiedName)
    (methodTypeSyntax : Syntax.Expr)
    (prevGlobals : Option Globals)
    (isDirty : Bool)
    : TCM Globals := do
  let ns ← TCM.getCurrentNamespace

  -- Check if we can reuse from previous globals
  if !isDirty then
    if let some prev := prevGlobals then
      if let some info := prev.getDef methodName then
        return globals.register ns methodName.display info

  -- Must elaborate fresh
  let methodType ← TCM.recoverWithM
    (elaborateMethodType globals typeClass methodTypeSyntax)
    (TCM.typePlaceholder Span.uninhabited)
  let methodInfo : GlobalInfo := {
    name := methodName
    type := methodType
    value := none
    isConstructor := false
    origin := .traitMethod
  }
  return globals.register ns methodName.display methodInfo

/-- Register or reuse a function entry -/
private def registerFunction
    (globals : Globals)
    (fn : Soma.Core.UntypedFunction)
    (prevGlobals : Option Globals)
    (isDirty : Bool)
    : TCM Globals := do
  let ns ← TCM.getCurrentNamespace

  -- Check if we can reuse from previous globals
  if !isDirty then
    if let some prev := prevGlobals then
      if let some info := prev.getDef fn.name then
        return globals.register ns fn.name.display info

  -- Must elaborate fresh
  let fnType ← TCM.recoverWithM
    (match fn.declaredTypeSyntax with
      | some typeSyntax => TCM.withGlobals globals (elaborateFunctionType typeSyntax)
      | none => TCM.freshMetaVal (.vType .zero))
    (TCM.typePlaceholder fn.span)
  let intrinsic ← inferIntrinsicInfo fn
  let info : GlobalInfo := {
    name := fn.name
    type := fnType
    value := none
    intrinsic := intrinsic
    isConstructor := false
    origin := match intrinsic with
      | some (.extern _) => if fn.attrs.intrinsic.isSome then .intrinsic else .extern
      | some _ => .intrinsic
      | none => .function
  }
  return globals.register ns fn.name.display info

/-- Build a `Globals` environment for a module -/
def buildGlobals
    (module : Soma.Core.UntypedModule)
    (prevGlobals : Option Globals := none)
    (dirtyNames : Std.HashSet String := {})
    : TCM Globals := do
  let ctx ← TCM.getCtx
  let ns := ctx.currentNamespace
  let mut globals := ctx.globals
  let isDirty (name : String) : Bool :=
    prevGlobals.isNone || dirtyNames.contains name

  -- First pass: Register all data type heads
  for typeDef in module.types do
    match typeDef with
    | .algebraic _ typeName binders _ headSort _ =>
      globals ← registerDataType globals typeName .algebraic binders #[] headSort prevGlobals (isDirty typeName.display)
    | .record _ recordName binders _ fields _ =>
      globals ← registerDataType globals recordName .record binders (fields.filterMap (·.1)) Soma.Core.Level.zero prevGlobals (isDirty recordName.display)

  -- Second pass: Register constructors
  for typeDef in module.types do
    match typeDef with
    | .algebraic _ typeName binders constructors _ _ =>
      let dirty := isDirty typeName.display
      for ctor in constructors do
        globals ← registerConstructor globals typeName binders ctor prevGlobals dirty
    | .record _ recordName binders ctorName fields _ =>
      let dirty := isDirty recordName.display
      globals ← registerRecordConstructor globals recordName binders ctorName fields prevGlobals dirty

  for typeDef in module.types do
    match typeDef with
    | .algebraic _ typeName _ _ _ typeSpan =>
      match globals.lookupInductive typeName with
      | some indMeta =>
        let ctorTypes := indMeta.ctors.map (·.type)
        match Totality.checkDataTypePositivity typeName.id ctorTypes typeSpan with
        | .ok => pure ()
        | .violated reason violationSpan =>
          let reportSpan :=
            if violationSpan == Span.uninhabited then typeSpan else violationSpan
          TCM.addError (.positivityViolation typeName.display reason reportSpan none)
      | none => pure ()
    | .record _ _ _ _ _ _ => pure ()

  for typeClass in module.typeClasses do
    globals ← registerTypeClassHead globals typeClass prevGlobals (isDirty typeClass.name.display)

  for typeClass in module.typeClasses do
    let classNameStr := typeClass.name.display
    let dirty := isDirty classNameStr
    let methodFieldNames := typeClass.methodSignatures.map (·.1.display)
    let typeVarNames := typeClass.params.map (·.name.name)
    if let some classQN := globals.resolve ns #[] classNameStr then
      globals := globals.registerInductive classQN .record typeVarNames methodFieldNames
      let fields := typeClass.methodSignatures.map (fun (name, ty) => (some name.display, ty))
      let ctorName ← do
        match prevGlobals with
        | some prev =>
          match prev.resolve ns #[classNameStr] "New" with
          | some prevCtorQN => pure prevCtorQN
          | none =>
            let u ← TCM.freshUnique "New"
            pure ⟨u⟩
        | none =>
          let u ← TCM.freshUnique "New"
          pure ⟨u⟩
      globals ← registerRecordConstructor globals typeClass.name typeClass.params ctorName fields prevGlobals dirty

  -- Type class methods
  for typeClass in module.typeClasses do
    let dirty := isDirty typeClass.name.display
    for (methodName, methodTypeSyntax) in typeClass.methodSignatures do
      globals ← registerMethod globals typeClass methodName methodTypeSyntax prevGlobals dirty

  -- Functions and theorems
  for fn in module.functions do
    globals ← registerFunction globals fn prevGlobals (isDirty fn.name.display)
  for thm in module.theorems do
    globals ← registerFunction globals thm prevGlobals (isDirty thm.name.display)

  globals ← indexWiredRoles module globals
  return globals

/-- Explicit incremental version of `buildGlobals` -/
def buildGlobalsIncremental
    (module : Soma.Core.UntypedModule)
    (prevGlobals : Globals)
    (dirtyNames : Std.HashSet String)
    : TCM Globals :=
  buildGlobals module (some prevGlobals) dirtyNames

end Soma.Dependent.Driver
