import Soma.Syntax
import Soma.Core.Module
import Soma.Core.Function
import Soma.Dependent.Monad
import Soma.Dependent.Infer
import Soma.Dependent.Unify
import Soma.Dependent.Level
import Soma.Dependent.Instance
import Soma.Dependent.Solver
import Soma.Dependent.Telescope
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

/-- Names eligible for auto-implicit binding in a signature -/
private def isAutoImplicitCandidate (name : String) : Bool :=
  match name.front? with
  | some c => c.isLower
  | none => false

/-- Collect every free identifier -/
def implicitForallNames (sigSyntax : Soma.Syntax.Expr) : TCM (List String) := do
  let freeVarNames := sigSyntax.freeVars.map (·.name)
  let mut acc : Array String := #[]
  for name in freeVarNames do
    if isBuiltinTypeName name then continue
    if (← TCM.lookupGlobal #[] name).isSome then continue
    if !isAutoImplicitCandidate name then continue
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

    let buildInner : TCM (Soma.Core.Expr ×
        Array (Soma.Unique × String × Value × Unique × Array Value) ×
        Option (Soma.Unique × String × Value × Unique × Array Value)) := do
      let superclasses := typeClass.superclasses
      let mut scBindings : Array (Soma.Unique × String × Value × Unique × Array Value) := #[]

      for (nameOpt, cstr) in superclasses do
        let head : Soma.Syntax.Expr := .con cstr.className
        let appExpr := cstr.args.foldl
          (fun acc a => Soma.Syntax.Expr.app acc a cstr.span) head
        let cstrTy ← elabTypeStandalone appExpr
        let dictName := match nameOpt with
          | some n => n.name
          | none => s!"$super_{cstr.className.name}"
        let dictUnique ← TCM.freshLocalId dictName
        let forcedTy ← Soma.Dependent.force cstrTy
        match Soma.Dependent.extractClassInfo? forcedTy with
        | some (classId, classArgs) =>
          scBindings := scBindings.push (dictUnique, dictName, cstrTy, classId, classArgs)
        | none => pure ()

      let classNameStr := typeClass.name.display
      let ns ← TCM.getCurrentNamespace
      let ctx ← TCM.getCtx
      let selfBindingOpt :
          Option (Soma.Unique × String × Value × Unique × Array Value) := ←
        match ctx.globals.resolve ns #[] classNameStr with
        | none => pure none
        | some classQN => do
          let mut traitParamVals : Array Value := #[]
          for i in [:P] do
            let pname := traitParamNames[i]!
            match ← TCM.lookupLocal pname with
            | some entry =>
              traitParamVals := traitParamVals.push
                (Value.vNeutral entry.type (.nVar ⟨pname, entry.level⟩))
            | none =>
              traitParamVals := traitParamVals.push (Value.vType Level.zero)
          let selfTy : Value := Value.vDataType classQN.id traitParamVals.toList
          let selfDictName := "$self"
          let selfDictUnique ← TCM.freshLocalId selfDictName
          pure (some (selfDictUnique, selfDictName, selfTy, classQN.id, traitParamVals))

      let allBindings := match selfBindingOpt with
        | some sb => scBindings.push sb
        | none => scBindings
      -- Total Pi-binder depth: own vars (M) + trait params (P) + super dicts (S) + self dict (1, when present)
      let scCount := scBindings.size
      let selfCount := if selfBindingOpt.isSome then 1 else 0
      let totalDepth := M + P + scCount + selfCount
      let rec withSCs (idx : Nat) : TCM Soma.Core.Expr := do
        if idx >= allBindings.size then
          let oldPostponed := (← TCM.getState).postponed
          let oldSet := oldPostponed.foldl
            (init := (∅ : Std.HashSet Soma.Core.ConstraintId))
            (fun acc tc => acc.insert tc.constraintId)
          let bodyExpr ← Soma.Dependent.inferTypeExpr methodTypeSyntax
          let bodyVal ← TCM.evalExpr bodyExpr
          TCM.modifyState fun s =>
            let kept := s.postponed.filter (fun tc => !oldSet.contains tc.constraintId)
            { s with postponed := kept }
          let report ← Soma.Dependent.solveConstraintsSoft
          report.allowPostponed
          TCM.modifyState fun s =>
            { s with postponed := oldPostponed ++ s.postponed }
          pure (Soma.Core.quoteExpr ⟨totalDepth⟩ bodyVal)
        else
          let (dictUnique, dictName, dictTy, _, _) := allBindings[idx]!
          Soma.Dependent.withLocalInstanceBinding dictName dictUnique dictTy
            .omega Span.uninhabited (withSCs (idx + 1))
      termination_by allBindings.size - idx

      let bodyExpr ← withSCs 0
      pure (bodyExpr, scBindings, selfBindingOpt)

    let ownWrapped ← ownBindings.foldrM (init := do
      traitBindings.foldrM (init := buildInner)
        (fun (uid, name, kind) acc =>
          pure (TCM.withBinding name uid kind .omega .implicit Span.uninhabited acc)))
      (fun (uid, name, kind) acc =>
        pure (TCM.withBinding name uid kind .omega .implicit Span.uninhabited acc))
    let innerInner ← ownWrapped
    let (innerBody, scBindings, selfBindingOpt) ← innerInner
    let scCount := scBindings.size

    -- own vars: 0 .. M-1
    -- trait params: M .. M+P-1
    -- super dicts: M+P .. M+P+scCount-1
    -- self dict: M+P+scCount (if present)
    let mut piExpr : Soma.Core.Expr := innerBody

    if let some (_, _, _, classQN, _) := selfBindingOpt then
      let argExprs : Array Soma.Core.Expr :=
        (List.range P).toArray.map (fun i => .bvar (P - 1 - i + scCount))
      let domExpr : Soma.Core.Expr := .dataTy classQN argExprs
      piExpr := .pi .omega .instance_ "$dict" domExpr piExpr

    for i in [:scCount] do
      let idx := scCount - 1 - i
      let (_, dictName, _, classQN, classArgs) := scBindings[idx]!
      let outerSuperCount := scCount - 1 - i
      let argExprs : Array Soma.Core.Expr := classArgs.map fun arg =>
        Soma.Core.quoteExpr ⟨P + outerSuperCount⟩ arg
      let domExpr : Soma.Core.Expr := .dataTy classQN argExprs
      piExpr := .pi .omega .instance_ dictName domExpr piExpr

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
        s!"@[intrinsic] on '{fn.name.display}' requires a tag string"
        fn.span .unknown)
    else
      match Intrinsic.fromTag? tag with
      | some i => pure (some i)
      | none => TCM.throw (.cannotInfer
          s!"unknown intrinsic tag '{tag}' on '{fn.name.display}'"
          fn.span .unknown)
  | none =>
    pure (fn.attrs.extern.map Intrinsic.extern)

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
      match ← tryUnfoldOneStep ty' with
      | some (u, _) => extractParamTypes u numParams
      | none => return (#[], ty')

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
        return (#[], ty)
      let dummyArg := Value.vNeutral dom (.nVar ⟨name, ⟨lvl⟩⟩)
      let codTy ← applyClosure cod dummyArg
      let remainingExplicit := if binder.isImplicit then numExplicit else numExplicit - 1
      let (restParams, resultTy) ← go codTy remainingExplicit (lvl + 1)
      return (#[(name, dom, binder, qty)] ++ restParams, resultTy)
    | _ =>
      if numExplicit > 0 then
        match ← tryUnfoldOneStep ty' with
        | some (u, _) => go u numExplicit lvl
        | none => return (#[], ty)
      else
        return (#[], ty)

/-- Extend the context with function parameters and run an action -/
def withFunctionParams (params : Array Soma.Core.FunctionParam) (paramTypes : Array Value)
    (span : Span) (action : TCM α) : TCM (Array (Soma.Unique × String) × α) := do
  -- First generate all local ids
  let mut bindings : Array (Soma.Unique × String) := #[]
  for p in params do
    let bindingId ← TCM.freshLocalId p.name
    bindings := bindings.push (bindingId, p.name)
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

/-- Like `withSignaturePrefixBindings`, but also returns the full value telescope used to publish an unfoldable NbE value -/
def withSignaturePrefixBindingsFull
    (allParams : Array (String × Value × Soma.Core.BinderInfo × Soma.Core.Quantity))
    (explicitParams : Array String)
    (span : Span) (action : TCM α)
    : TCM (Array (Soma.Unique × String)
        × Array Soma.Core.ValueParam × α) := do
  let mut allBindings : Array (Soma.Unique × String × Soma.Core.BinderInfo × Soma.Core.Quantity) := #[]
  let mut valueBindings : Array Soma.Core.ValueParam := #[]
  let mut eIdx : Nat := 0
  for (name, ty, binder, qty) in allParams do
    if binder.isImplicit then
      let bindingId ← TCM.freshLocalId name
      allBindings := allBindings.push (bindingId, name, binder, qty)
      valueBindings := valueBindings.push { uid := bindingId, name, binder, type := ty }
    else
      let paramName := if h : eIdx < explicitParams.size then explicitParams[eIdx] else name
      let bindingId ← TCM.freshLocalId paramName
      allBindings := allBindings.push (bindingId, paramName, .explicit, qty)
      valueBindings := valueBindings.push
        { uid := bindingId, name := paramName, binder := .explicit, type := ty }
      eIdx := eIdx + 1
  let rec go (idx : Nat) : TCM α := do
    if idx >= allBindings.size then
      action
    else
      let (bindingId, paramName, binder, qty) := allBindings[idx]!
      let (_, ty, _, _) := allParams[idx]!
      withCheckedBinding paramName bindingId ty qty binder span do
        if binder == .instance_ then
          Soma.Dependent.withLocalInstanceForBoundDict
            paramName bindingId ty span (go (idx + 1))
        else
          go (idx + 1)
  let result ← go 0
  let runtimeBindings : Array (Soma.Unique × String) := valueBindings.filterMap fun vp =>
    if vp.binder.isImplicit && vp.type.isKind then none
    else some (vp.uid, vp.name)
  return (runtimeBindings, valueBindings, result)

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
    let report ← Soma.Dependent.solveConstraintsSoft
    report.allowPostponed
    let bodyVal ← TCM.evalExpr bodyExpr
    let bodyVal' ← zonkValue bodyVal
    pure (Soma.Core.quoteExpr ⟨N⟩ bodyVal')
  let wrapped ← bindingIds.foldrM (init := go)
    (fun (uid, name) acc => pure (TCM.withBinding name uid tyTy .omega .implicit Span.uninhabited acc))
  let closedBodyExpr ← wrapped

  let mut piExpr : Soma.Core.Expr := closedBodyExpr
  for i in [:N] do
    let idx := N - 1 - i
    let name := freeVarNamesUnique[idx]!
    piExpr := Soma.Core.Expr.pi .omega .implicit name (.sort Level.zero) piExpr
  let fnType ← TCM.evalExprInEnv Soma.Core.Env.empty piExpr

  let report ← Soma.Dependent.solveConstraintsSoft
  report.allowPostponed
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
  : TCM (Value × Soma.Core.Expr × Array (Soma.Unique × String)
      × Array Soma.Core.ValueParam × Bool) := do
  let span := fn.span
  let storedType : Option Value ← match ← TCM.lookupGlobalByQN fn.name with
    | some info => pure (some info.type)
    | none => pure none
  if (fn.attrs.intrinsic.isSome || fn.attrs.extern.isSome) && fn.isExternStub then
    match fn.declaredTypeSyntax with
    | some _ =>
      let declaredType ← match storedType with
        | some ty => pure ty
        | none =>
          TCM.freshMetaVal (.vType .zero)
            (displayHint := some s!"return:{fn.name.display}")
      Soma.Dependent.drainConstraints
      let declaredType' ← zonkValue declaredType
      reportUnsolvedMetas declaredType' span
      let declaredType'' ← expandAbbrevValue declaredType'
      return (declaredType'', Soma.Core.TypedFunction.externBody fn.name, #[], #[], false)
    | none =>
      let ty ← TCM.freshMetaVal (.vType .zero)
        (displayHint := some s!"return:{fn.name.display}")
      return (ty, Soma.Core.TypedFunction.externBody fn.name, #[], #[], false)
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
      return (declaredType'', Soma.Core.TypedFunction.erroredBody fn.name, #[], #[], true)
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
      return (resolved', Soma.Core.TypedFunction.erroredBody fn.name, #[], #[], true)
    | some body =>
      let bodyIsProof ← Soma.Dependent.valueInPropUniverse resultType
      let runBodyCheck : TCM Soma.Core.Expr :=
        TCM.withOrigin (.returnType fn.name.display body.span) <|
          TCM.infallible (Soma.Dependent.checkSyntax body resultType) default
      let (generatedParams, valueParams, zonkedBody) ← withSignaturePrefixBindingsFull allParams fn.paramNames span do
        let bodyExpr ← if bodyIsProof then TCM.inErasedContext runBodyCheck else runBodyCheck
        Soma.Dependent.drainConstraints
        zonkExpr bodyExpr
      let declaredType' ← zonkValue declaredType
      reportUnsolvedMetas declaredType' span
      let typedBody' := zonkedBody.betaReduce
      Soma.Dependent.zonkLocalTypesInPlace
      let declaredType'' ← expandAbbrevValue declaredType'
      return (declaredType'', typedBody', generatedParams, valueParams, false)
  | none =>
    let paramTypes ← fn.params.mapM fun param => do
      match param.typeSyntax with
      | some tySyntax =>
        TCM.recoverWithM (elaborateFunctionType tySyntax) (TCM.typePlaceholder span)
      | none =>
        TCM.freshMetaVal (.vType .zero)
          (displayHint := some s!"type:{param.name}")
    let (generatedParams, (inferredType, zonkedBody)) ← withFunctionParams fn.params paramTypes span do
      let (inferredType, typedBody) ← TCM.infallibleExpr (Soma.Dependent.inferSyntax fn.body) span
      Soma.Dependent.drainConstraints
      let zonked ← zonkExpr typedBody
      pure (inferredType, zonked)
    let inferredType' ← zonkValue inferredType
    reportUnsolvedMetas inferredType' span
    let typedBody' := zonkedBody.betaReduce
    Soma.Dependent.zonkLocalTypesInPlace
    -- Expand parameterized type abbreviations so downstream passes see real types
    let inferredType'' ← expandAbbrevValue inferredType'
    let zonkedParamTypes ← paramTypes.mapM zonkValue
    let valueParams : Array Soma.Core.ValueParam ← generatedParams.mapIdxM fun idx (u, n) => do
      let ty := if h : idx < zonkedParamTypes.size then zonkedParamTypes[idx] else .vType .zero
      pure { uid := u, name := n, binder := .explicit, type := ty }
    return (inferredType'', typedBody', generatedParams, valueParams, false)

/-- Elaborate a constructor type -/
def elaborateCtorType (typeName : Soma.Core.QualifiedName)
    (typeVarBinders : Array Syntax.TypeVarBinder)
    (fieldTypeSyntax : Array Syntax.Expr)
    (fieldBinderInfos : Array Soma.Core.BinderInfo := #[])
    (fieldQuantities : Array Soma.Core.Quantity := #[])
    (fieldNames : Array String := #[]) : TCM Value := do
  let N := typeVarBinders.size
  let M := fieldTypeSyntax.size

  let fieldBI (i : Nat) : Soma.Core.BinderInfo :=
    fieldBinderInfos[i]?.getD .explicit
  let fieldQty (i : Nat) : Soma.Core.Quantity :=
    fieldQuantities[i]?.getD .omega
  let fieldNm (i : Nat) : String :=
    fieldNames[i]?.getD "_"

  let paramQty (i : Nat) : Soma.Core.Quantity :=
    if h : i < typeVarBinders.size then typeVarBinders[i].quantity else .omega
  let binderBI (i : Nat) : Soma.Core.BinderInfo :=
    if h : i < typeVarBinders.size then
      let b := typeVarBinders[i]
      if b.isConstraint then .instance_ else .implicit
    else .implicit

  let resultExpr (depth : Nat) (paramVals : Array Value) : TCM Soma.Core.Expr := do
    pure (Soma.Core.quoteExpr ⟨depth⟩ (Value.vDataType typeName.id paramVals.toList))

  let rec processFields (i : Nat) (paramVals : Array Value) : TCM Soma.Core.Expr := do
    if h : i < fieldTypeSyntax.size then
      let fieldTy := fieldTypeSyntax[i]
      let fieldExpr ← Soma.Dependent.inferTypeExpr fieldTy
      let fieldVal ← TCM.evalExpr fieldExpr
      let bi := fieldBI i
      let qty := fieldQty i
      let fname := fieldNm i
      let uid ← TCM.freshLocalId fname
      TCM.withBinding fname uid fieldVal qty bi Span.uninhabited do
        let act := processFields (i + 1) paramVals
        let inner ←
          if bi == .instance_ then
            Soma.Dependent.withLocalInstanceForBoundDict fname uid fieldVal Span.uninhabited act
          else act
        pure (.pi qty bi fname fieldExpr inner)
    else
      let report ← Soma.Dependent.solveConstraintsSoft
      report.allowPostponed
      resultExpr (N + M) paramVals
  termination_by fieldTypeSyntax.size - i

  let rec processBinders (i : Nat) (paramVals : Array Value)
      (kindExprs : Array Soma.Core.Expr)
      : TCM (Soma.Core.Expr × Array Soma.Core.Expr) := do
    if h : i < typeVarBinders.size then
      let binder := typeVarBinders[i]
      let kindExpr ← match binder with
        | .mk _ (some k) _ _ => Soma.Dependent.inferTypeExpr k
        | .mk _ none _ _ => pure (.sort Level.zero)
        | .constraint _ cstr =>
          let head : Soma.Syntax.Expr := .con cstr.className
          let appExpr := cstr.args.foldl
            (fun acc a => Soma.Syntax.Expr.app acc a cstr.span) head
          Soma.Dependent.inferTypeExpr appExpr
      let kindVal ← TCM.evalExpr kindExpr
      let qty := paramQty i
      let bi := binderBI i
      let uid ← TCM.freshLocalId binder.name.name
      let kindExprs' := kindExprs.push kindExpr
      TCM.withBinding binder.name.name uid kindVal qty bi Span.uninhabited do
        let lvl ← TCM.currentLevel
        let paramVals' :=
          paramVals.push (Value.vNeutral kindVal (.nVar ⟨binder.name.name, ⟨lvl.lvl - 1⟩⟩))
        let act := processBinders (i + 1) paramVals' kindExprs'
        if bi == .instance_ then
          Soma.Dependent.withLocalInstanceForBoundDict
            binder.name.name uid kindVal Span.uninhabited act
        else act
    else
      let body ← processFields 0 paramVals
      pure (body, kindExprs)
  termination_by typeVarBinders.size - i
  let (innerBody, paramKindExprs) ← processBinders 0 #[] #[]

  let mut piExpr : Soma.Core.Expr := innerBody
  for i in [:N] do
    let idx := N - 1 - i
    let name := typeVarBinders[idx]!.name.name
    let kindExpr := paramKindExprs[idx]!
    piExpr := .pi (paramQty idx) (binderBI idx) name kindExpr piExpr
  TCM.evalExprInEnv Soma.Core.Env.empty piExpr

/-- Elaborate an indexed constructor type from a full user-written signature -/
def elaborateIndexedCtorType (_typeName : Soma.Core.QualifiedName)
    (typeVarBinders : Array Syntax.TypeVarBinder) (paramCount : Nat)
    (sigSyntax : Syntax.Expr) : TCM Value := do
  let P := min paramCount typeVarBinders.size
  let paramNames : Array String :=
    (Array.range P).map (fun i => typeVarBinders[i]!.name.name)

  let rec drive (i : Nat) (acc : Array (Soma.Core.Expr × Soma.Core.Quantity × String))
      : TCM Soma.Core.Expr := do
    if h : i < P then
      let binder := typeVarBinders[i]!
      let kindExpr ← match binder.kind with
        | some k => Soma.Dependent.inferTypeExpr k
        | none   => pure (.sort Level.zero)
      let kindVal ← TCM.evalExpr kindExpr
      let bi := binder.binderInfo
      let qty : Soma.Core.Quantity ← match binder.quantity with
        | .zero => pure .zero
        | .one  => pure .one
        | .omega =>
          if (← Soma.Dependent.shouldAutoEraseBinder kindVal) then pure .zero
          else pure .omega
      let pname := binder.name.name
      let uid ← TCM.freshLocalId pname
      TCM.withBinding pname uid kindVal qty bi Span.uninhabited do
        drive (i + 1) (acc.push (kindExpr, qty, pname))
    else
      let allFree ← implicitForallNames sigSyntax
      let freeVarNamesUnique := allFree.filter (fun n => !paramNames.contains n)

      let tyTy : Value := Value.vType Level.zero
      let M := freeVarNamesUnique.length

      let mut autoBindings : Array (Soma.Unique × String × Value) := #[]
      for varName in freeVarNamesUnique do
        let uid ← TCM.freshLocalId varName
        let kindMeta ← TCM.freshMetaVal tyTy
        autoBindings := autoBindings.push (uid, varName, kindMeta)

      let buildInner : TCM Soma.Core.Expr := do
        let bodyExpr ← Soma.Dependent.inferTypeExpr sigSyntax
        let bodyVal ← TCM.evalExpr bodyExpr
        pure (Soma.Core.quoteExpr ⟨P + M⟩ bodyVal)

      let wrapped ← autoBindings.foldrM (init := buildInner)
        (fun (uid, name, kind) acc =>
          pure (TCM.withBinding name uid kind .omega .implicit Span.uninhabited acc))
      let innerBody ← wrapped

      -- Wrap with auto-implicit forall Pis (innermost layer).
      let mut piExpr : Soma.Core.Expr := innerBody
      for i in [:M] do
        let idx := M - 1 - i
        let name := freeVarNamesUnique[idx]!
        let (_, _, kindVal) := autoBindings[idx]!
        let kindExpr ← do
          let zonked ← zonkValue kindVal
          pure (Soma.Core.quoteExpr0 zonked)
        piExpr := .pi .omega .implicit name kindExpr piExpr

      for i in [:P] do
        let idx := P - 1 - i
        let (kindExpr, qty, pname) := acc[idx]!
        piExpr := .pi qty .implicit pname kindExpr piExpr
      pure piExpr
  termination_by P - i

  let piExpr ← drive 0 #[]
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
          TCM.throw (.cannotInfer s!"unknown wired_in role '{roleName}' on {what}" attr.span .unknown)
        | some role =>
          let existing := g.wiredIn.getAll role
          let conflicts := existing.filter (fun e => e.name != info.name)
          if conflicts.isEmpty then
            g := { g with wiredIn := g.wiredIn.register role info }
          else
            let prev := String.intercalate ", " ((conflicts.map (fun e => e.name.display)).toList)
            TCM.throw (.cannotInfer s!"duplicate wired_in role '{role.canonical}' on {what}; already bound to {prev}" attr.span .unknown)
      | _ =>
        TCM.throw (.cannotInfer s!"@[wired_in] on {what} requires a string literal role argument" attr.span .unknown)
  pure g

private def indexWiredRoles (module : Soma.Core.UntypedModule) (globals : Globals) : TCM Globals := do
  let mut g := globals
  for typeDef in module.types do
    match typeDef with
    | .algebraic attrs typeName _ _ ctors _ _ =>
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
            TCM.throw (.cannotInfer s!"duplicate wired_in role '{role.canonical}' on function {fn.name.display}; already bound to {prev}" fn.span .unknown)
        | none =>
          TCM.throw (.cannotInfer s!"unknown wired_in role '{roleName}' on function {fn.name.display}" fn.span .unknown)
  pure g

/-- Elaborate a type constructor's head kind from its parameter binders -/
def elaborateTypeHeadKind
    (binders : Array Syntax.TypeVarBinder)
    (resultSort : Soma.Core.Level := Level.zero) : TCM Value := do
  let rec loop (i : Nat)
      (acc : Array (String × Soma.Core.Expr × Soma.Core.Quantity × Soma.Core.BinderInfo))
      : TCM (Array (String × Soma.Core.Expr × Soma.Core.Quantity × Soma.Core.BinderInfo)) := do
    if h : i < binders.size then
      let binder := binders[i]
      let kindExpr ← match binder.kind with
        | some k => Soma.Dependent.inferTypeExpr k
        | none   => pure (.sort Level.zero)
      let kindVal ← TCM.evalExpr kindExpr
      let bi := binder.binderInfo
      let qty : Soma.Core.Quantity ← match binder.quantity with
        | .zero => pure .zero
        | .one => pure .one
        | .omega =>
          if (← Soma.Dependent.shouldAutoEraseBinder kindVal) then pure .zero
          else pure .omega
      let acc' := acc.push (binder.name.name, kindExpr, qty, bi)
      let uid ← TCM.freshLocalId binder.name.name
      TCM.withBinding binder.name.name uid kindVal qty bi Span.uninhabited do
        loop (i + 1) acc'
    else
      pure acc
  let paramKinds ← loop 0 #[]
  let mut headKindExpr : Soma.Core.Expr := .sort resultSort
  for (paramName, paramKindExpr, qty, bi) in paramKinds.reverse do
    headKindExpr := .pi qty bi paramName paramKindExpr headKindExpr
  TCM.evalExprInEnv Soma.Core.Env.empty headKindExpr

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
    (TCM.withGlobals g (elaborateTypeHeadKind typeClass.params))
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

/-- Pre-register all type names from a module -/
def preRegisterTypes (module : Soma.Core.UntypedModule) : TCM Globals := do
  let ctx ← TCM.getCtx
  let ns := ctx.currentNamespace
  let mut globals := ctx.globals
  for typeDef in module.types do
    match typeDef with
    | .algebraic _ typeName binders _ _ headSort _ =>
      let typeQN := typeName
      let headKind ← TCM.withGlobals globals (elaborateTypeHeadKind binders headSort)
      globals := globals.registerInductive typeQN .algebraic
        (binders.map (·.name.name)) #[] #[] headSort
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
      let sourceFieldNames := fields.map (fun f => f.name.getD "_")
      let sourceFieldQuantities := fields.map (·.quantity)
      globals := globals.registerInductive typeQN .record
        (binders.map (·.name.name))
        sourceFieldNames
        sourceFieldQuantities
      let dataTypeInfo : GlobalInfo := {
        name := typeQN
        type := headKind
        value := some (Value.vDataType typeQN.id [])
        isConstructor := false
        origin := .typeDecl
      }
      globals := globals.register ns recordName.display dataTypeInfo
  for typeClass in module.typeClasses do
    let classQN := typeClass.name
    let headKind ← TCM.withGlobals globals
      (elaborateTypeHeadKind typeClass.params)
    let classInfo : GlobalInfo := {
      name := classQN
      type := headKind
      value := some (Value.vDataType classQN.id [])
      isConstructor := false
      origin := .class_
    }
    globals := globals.register ns classQN.display classInfo
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
      let info' := { info with type := zonked }
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
    (fieldQuantities : Array Soma.Core.Quantity := #[])
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
          g := g.registerInductive prevQN kind typeVarNames fieldNames fieldQuantities
          return g

  let headKind ← TCM.withGlobals globals (elaborateTypeHeadKind binders headSort)
  let mut g := globals.registerInductive typeQN kind typeVarNames fieldNames fieldQuantities headSort
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
    (paramCount : Nat)
    (ctorQN : Soma.Core.QualifiedName)
    (ctorSimpleName : String)
    (ctorTag : Nat)
    (fieldTypes : Array Syntax.Expr)
    (sigSyntax : Option Syntax.Expr)
    (prevGlobals : Option Globals)
    (isDirty : Bool)
    (fieldBinderInfos : Array Soma.Core.BinderInfo := #[])
    (fieldQuantities : Array Soma.Core.Quantity := #[])
    (fieldNames : Array String := #[])
    : TCM Globals := do
  let ns ← TCM.getCurrentNamespace
  let typeNs := ns.push typeName.display

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

  let paramBinders := typeVarBinders.extract 0 paramCount
  let ctorType ← TCM.recoverWithM
    (match sigSyntax with
      | some sig => TCM.withGlobals globals
          (elaborateIndexedCtorType typeName typeVarBinders paramCount sig)
      | none => TCM.withGlobals globals
          (elaborateCtorType typeName paramBinders fieldTypes
            fieldBinderInfos fieldQuantities fieldNames))
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
    (paramCount : Nat)
    (ctor : Soma.Core.UntypedConstructor)
    (prevGlobals : Option Globals)
    (isDirty : Bool)
    : TCM Globals :=
  registerConstructorRaw globals typeName typeVarBinders paramCount
    ctor.name ctor.name.id.original ctor.tag ctor.fieldTypeSyntax ctor.sigSyntax
    prevGlobals isDirty
    (fieldBinderInfos := ctor.fieldBinderInfos)
    (fieldQuantities := ctor.fieldQuantities)
    (fieldNames := ctor.fieldNames)

/-- Register or reuse record field accessors, returns updated globals -/
private def registerRecordFieldAccessors
    (globals : Globals)
    (recordName : Soma.Core.QualifiedName)
    (fields : Array Soma.Core.RecordFieldDef)
    (prevGlobals : Option Globals)
    (isDirty : Bool)
    : TCM Globals := do
  let ns ← TCM.getCurrentNamespace
  let typeNs := ns.push recordName.display
  let mut g := globals

  if !isDirty then
    if let some prev := prevGlobals then
      for f in fields do
        if let some fieldName := f.name then
          if let some accQN := prev.resolve ns #[recordName.display] fieldName then
            if let some accessorInfo := prev.getDef accQN then
              g := g.register typeNs fieldName accessorInfo
      return g

  for f in fields do
    if let some fieldName := f.name then
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
    (fields : Array Soma.Core.RecordFieldDef)
    (prevGlobals : Option Globals)
    (isDirty : Bool)
    : TCM Globals := do
  let g ← registerConstructorRaw globals recordName typeVarBinders typeVarBinders.size
    ctorName "New" 0 (fields.map (·.type)) none prevGlobals isDirty
    (fieldBinderInfos := fields.map (·.binderInfo))
    (fieldQuantities := fields.map (·.quantity))
    (fieldNames := fields.map (fun f => f.name.getD "_"))
  registerRecordFieldAccessors g recordName fields prevGlobals isDirty

/-- Elaborate a type class method type -/
private def elaborateMethodType
    (globals : Globals)
    (typeClass : Soma.Core.TypeClassMeta)
    (methodTypeSyntax : Syntax.Expr)
    : TCM Value :=
  elaborateTraitMethodType globals typeClass methodTypeSyntax

/-- Walk a method type collecting pi binders along with its domain quoted as a Core `Expr` -/
private partial def collectMethodBinders (ty : Soma.Core.Value)
    : Array (Soma.Core.Quantity × Soma.Core.BinderInfo × String × Soma.Core.Expr) :=
  go ty 0 #[]
where
  go (ty : Soma.Core.Value) (depth : Nat)
      (acc : Array (Soma.Core.Quantity × Soma.Core.BinderInfo × String × Soma.Core.Expr))
      : Array (Soma.Core.Quantity × Soma.Core.BinderInfo × String × Soma.Core.Expr) :=
    match ty with
    | .vPi qty binder name dom cod =>
      let domExpr := Soma.Core.quoteExpr ⟨depth⟩ dom
      let argVal := Soma.Core.Value.vNeutral dom (Soma.Core.Neutral.nVar ⟨name, ⟨depth⟩⟩)
      let nextTy := cod.applyPure argVal
      go nextTy (depth + 1) (acc.push (qty, binder, name, domExpr))
    | _ => acc

/-- Build the auto-projection body Core for a class method -/
private def buildClassMethodAutoProjValue
    (methodSimpleName : String) (fieldIdx : Nat) (methodType : Soma.Core.Value)
    : Option Soma.Core.Expr := Id.run do
  let binders := collectMethodBinders methodType
  let total := binders.size
  if total == 0 then return none
  -- Find the last instance binder (the self-class dict).
  let mut dictPos? : Option Nat := none
  for h : i in [:total] do
    let (_, binder, _, _) := binders[i]
    if binder == .instance_ then dictPos? := some i
  match dictPos? with
  | none => return none
  | some pos =>
    let dictBVar := total - pos - 1
    let head : Soma.Core.Expr :=
      Soma.Core.Expr.fieldAccess (.bvar dictBVar) methodSimpleName fieldIdx
    let mut body := head
    for h : p in [pos + 1 : total] do
      let argBVar := total - p - 1
      body := .app body (.bvar argBVar)
    let mut result := body
    for h : i in [:total] do
      let idx := total - 1 - i
      let (_qty, binder, name, domExpr) := binders[idx]!
      result := .lam binder name domExpr result
    return some result

/-- Register or reuse a type class method, returns updated globals -/
private def registerMethod
    (globals : Globals)
    (typeClass : Soma.Core.TypeClassMeta)
    (methodName : Soma.Core.QualifiedName)
    (methodTypeSyntax : Syntax.Expr)
    (fieldIdx : Nat)
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
  let methodValue? : Option Soma.Core.Value :=
    (buildClassMethodAutoProjValue methodName.id.original fieldIdx methodType).map
      Soma.Core.evalClosed
  let methodInfo : GlobalInfo := {
    name := methodName
    type := methodType
    value := methodValue?
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
    | .algebraic _ typeName binders _ ctors headSort _ =>
      let (structFieldNames, structFieldQuantities) :=
        match ctors[0]? with
        | some ctor =>
          if ctors.size == 1
             && ctor.fieldNames.size > 0
             && ctor.fieldNames.all (· != "_") then
            (ctor.fieldNames, ctor.fieldQuantities)
          else
            (#[], #[])
        | none => (#[], #[])
      globals ← registerDataType globals typeName .algebraic binders
        structFieldNames structFieldQuantities headSort prevGlobals
        (isDirty typeName.display)
    | .record _ recordName binders _ fields _ =>
      let sourceFieldNames := fields.map (fun f => f.name.getD "_")
      let sourceFieldQuantities := fields.map (·.quantity)
      globals ← registerDataType globals recordName .record binders sourceFieldNames sourceFieldQuantities Soma.Core.Level.zero prevGlobals (isDirty recordName.display)

  for typeClass in module.typeClasses do
    globals ← registerTypeClassHead globals typeClass prevGlobals (isDirty typeClass.name.display)

  -- Second pass: Register constructors
  for typeDef in module.types do
    match typeDef with
    | .algebraic _ typeName binders paramCount constructors _ _ =>
      let dirty := isDirty typeName.display
      for ctor in constructors do
        globals ← registerConstructor globals typeName binders paramCount ctor prevGlobals dirty
    | .record _ recordName binders ctorName fields _ =>
      let dirty := isDirty recordName.display
      globals ← registerRecordConstructor globals recordName binders ctorName fields prevGlobals dirty

  for typeDef in module.types do
    match typeDef with
    | .algebraic _ typeName _ _ _ _ typeSpan =>
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
    let dirty := isDirty typeClass.name.display
    let superOffset := typeClass.superclasses.size
    for h : i in [:typeClass.methodSignatures.size] do
      let (methodName, methodTypeSyntax) := typeClass.methodSignatures[i]
      globals ← registerMethod globals typeClass methodName methodTypeSyntax (superOffset + i) prevGlobals dirty

  for typeClass in module.typeClasses do
    let classNameStr := typeClass.name.display
    let dirty := isDirty classNameStr
    let mut superFieldSpecs : Array (String × Soma.Syntax.Expr) := #[]
    for (_, cstr) in typeClass.superclasses do
      match globals.resolve ns cstr.className.path cstr.className.name with
      | some superQN =>
        let head : Soma.Syntax.Expr := .con cstr.className
        let tyExpr := cstr.args.foldl
          (fun acc a => Soma.Syntax.Expr.app acc a cstr.span) head
        superFieldSpecs := superFieldSpecs.push
          (s!"$super_{superQN.id.original}", tyExpr)
      | none =>
        TCM.addError (.unknownClass cstr.className.name cstr.span)
    let superFieldNames := superFieldSpecs.map (·.1)
    let methodFieldNames := superFieldNames ++ typeClass.methodSignatures.map (·.1.display)
    let typeVarNames := typeClass.params.map (·.name.name)
    if let some classQN := globals.resolve ns #[] classNameStr then
      let methodFieldQuantities := methodFieldNames.map fun _ => Soma.Core.Quantity.omega
      globals := globals.registerInductive classQN .record typeVarNames methodFieldNames methodFieldQuantities
      let fields : Array Soma.Core.RecordFieldDef :=
        -- Superclass dictionaries are `.instance_` fields
        (superFieldSpecs.map fun (nm, tyExpr) =>
          { name := some nm, type := tyExpr, binderInfo := .instance_ }) ++
        typeClass.methodSignatures.map fun (name, ty) =>
          { name := some name.display, type := ty }
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

  globals ← indexWiredRoles module globals
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
