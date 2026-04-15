import Soma.Syntax
import Soma.Core.Module
import Soma.Core.Function
import Soma.Dependent.Monad
import Soma.Dependent.Infer
import Soma.Dependent.Unify
import Soma.Dependent.Level
import Soma.Dependent.Instance
import Soma.Dependent.Error
import Soma.Dependent.Totality
import Soma.Dependent.Elaborate
import Soma.Dependent.TraitElaborate
import Soma.Dependent.Zonk
import Soma.Core.Eval

namespace Soma.Dependent.Driver

open Soma.Syntax
open Soma.Core (Value Level PrimOp FFIOp Intrinsic)
open Soma (UniqueSupply)

/-- Replace dangling bvar references in fvar type annotations with stable
    sentinel fvar references that preserve de Bruijn level identity -/
partial def resolveErasedTypeBvars (e : Soma.Core.Expr)
    (depth : Nat) (erasedParams : Array (Nat × String)) : Soma.Core.Expr :=
  match e with
  | .fvar u tyExpr =>
    .fvar u (resolveTyExpr tyExpr depth erasedParams)
  | .app f a =>
    .app (resolveErasedTypeBvars f depth erasedParams)
         (resolveErasedTypeBvars a depth erasedParams)
  | .lam i n d b =>
    .lam i n (resolveTyExpr d depth erasedParams)
             (resolveErasedTypeBvars b (depth + 1) erasedParams)
  | .let_ n t v b =>
    .let_ n (resolveTyExpr t depth erasedParams)
            (resolveErasedTypeBvars v depth erasedParams)
            (resolveErasedTypeBvars b (depth + 1) erasedParams)
  | .«case» scruts arms rty =>
    .«case» (scruts.map (resolveErasedTypeBvars · depth erasedParams))
            (arms.map fun arm =>
              let binds := arm.patterns.foldl (fun a p => a + p.bindingCount) 0
              Soma.Core.Arm.mk arm.patterns (resolveErasedTypeBvars arm.body (depth + binds) erasedParams))
            (resolveTyExpr rty depth erasedParams)
  | .if_ c t el =>
    .if_ (resolveErasedTypeBvars c depth erasedParams)
         (resolveErasedTypeBvars t depth erasedParams)
         (resolveErasedTypeBvars el depth erasedParams)
  | .construct qn tag args rty =>
    .construct qn tag (args.map (resolveErasedTypeBvars · depth erasedParams))
                      (resolveTyExpr rty depth erasedParams)
  | .inject l args rty =>
    .inject l (args.map (resolveErasedTypeBvars · depth erasedParams))
              (resolveTyExpr rty depth erasedParams)
  | .record fields =>
    .record (fields.map fun (n, e') => (n, resolveErasedTypeBvars e' depth erasedParams))
  | .pair f s =>
    .pair (resolveErasedTypeBvars f depth erasedParams)
          (resolveErasedTypeBvars s depth erasedParams)
  | .array es ety =>
    .array (es.map (resolveErasedTypeBvars · depth erasedParams))
           (resolveTyExpr ety depth erasedParams)
  | .closure n caps =>
    .closure n (caps.map (resolveErasedTypeBvars · depth erasedParams))
  | .ann x t =>
    .ann (resolveErasedTypeBvars x depth erasedParams) (resolveTyExpr t depth erasedParams)
  | other => other
where
  /-- Replace bvar references to erased type params in a type expression -/
  resolveTyExpr (te : Soma.Core.Expr) (d : Nat) (params : Array (Nat × String))
      : Soma.Core.Expr :=
    match te with
    | .bvar idx =>
      -- A param at de Bruijn level L has bvar index (d - L - 1) at depth d
      let found := params.find? fun (level, _) => d > level && idx == d - level - 1
      match found with
      | some (level, name) => .fvar ⟨level, "__tyvar", name⟩ (.sort .zero)
      | none => te
    | .pi q bi n dom cod =>
      .pi q bi n (resolveTyExpr dom d params) (resolveTyExpr cod (d + 1) params)
    | .app f a => .app (resolveTyExpr f d params) (resolveTyExpr a d params)
    | .sigma q bi n f s =>
      .sigma q bi n (resolveTyExpr f d params) (resolveTyExpr s (d + 1) params)
    | .dataTy uid ps => .dataTy uid (ps.map (resolveTyExpr · d params))
    | .fvar u ty => .fvar u (resolveTyExpr ty d params)
    | .rowExtend l ft t =>
      .rowExtend (resolveTyExpr l d params) (resolveTyExpr ft d params) (resolveTyExpr t d params)
    | .recordTy r => .recordTy (resolveTyExpr r d params)
    | .variantTy r => .variantTy (resolveTyExpr r d params)
    | .eqTy lv t l r =>
      .eqTy lv (resolveTyExpr t d params) (resolveTyExpr l d params) (resolveTyExpr r d params)
    | other => other

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
  let ty' ← force ty
  match ty' with
  | .vPi qty binder name dom cod =>
    -- Once we consumed all explicit term parameters, stop before the next explicit binder
    if numExplicit == 0 && !binder.isImplicit then
      return (#[], ty')
    let lvl ← TCM.currentLevel
    let dummyArg := Value.vNeutral dom (.nVar ⟨name, lvl⟩)
    let codTy ← applyClosure cod dummyArg
    let remainingExplicit := if binder.isImplicit then numExplicit else numExplicit - 1
    let (restParams, resultTy) ← extractSignaturePrefix codTy remainingExplicit
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

/-- Elaborate a function type signature with implicit quantification of free type variables -/
def elaborateFunctionType (sigSyntax : Syntax.TypeExpr) : TCM Value := do
  -- Find all free type variables in the function signature
  let freeVarNames := sigSyntax.freeVars.map (·.name)
  let freeVarNamesUnique := freeVarNames.toList.eraseDups

  -- Create an elaboration environment with all free type variables bound
  let mut elabEnv := Elaborate.ElabEnv.empty
  for varName in freeVarNamesUnique do
    elabEnv := elabEnv.extend varName (.vType .zero)

  -- Elaborate the function type body
  let fnBodyType ← Elaborate.elaborateType elabEnv sigSyntax

  -- Wrap in implicit foralls for all free type variables (right to left)
  let mut fnType := fnBodyType
  for varName in freeVarNamesUnique.reverse do
    let outerEnv : Elaborate.ElabEnv := {
      tyVars := elabEnv.tyVars.tail!
      level := elabEnv.level - 1
    }
    let codClosure ← Elaborate.mkDependentClosure varName fnType outerEnv
    fnType := Value.vPi .omega .implicit varName (.vType .zero) codClosure
    elabEnv := outerEnv

  return fnType

/-- Type check a single function using dependent types.
    Returns (fnType, typedBody, generatedParams) where generatedParams contains local ids. -/
def checkFunction (fn : Soma.Core.UntypedFunction)
  : TCM (Value × Soma.Core.Expr × Array (Soma.Unique × String)) := do
  let span := fn.span
  -- Intrinsic/extern functions have no real body — just elaborate the type
  if fn.attrs.intrinsic.isSome || fn.attrs.extern.isSome then
    match fn.declaredTypeSyntax with
    | some typeSyntax =>
      let declaredType ← TCM.recoverWithM
        (elaborateFunctionType typeSyntax)
        (TCM.typePlaceholder span)
      let placeholderBody := Soma.Core.Expr.lit (.string s!"placeholder:{fn.name.display}")
      -- Expand abbreviations in intrinsic/extern types too
      let declaredType' ← expandAbbrevValue declaredType
      return (declaredType', placeholderBody, #[])
    | none =>
      let ty ← TCM.freshMetaVal (.vType .zero)
      let placeholderBody := Soma.Core.Expr.lit (.string s!"placeholder:{fn.name.display}")
      return (ty, placeholderBody, #[])
  match fn.declaredTypeSyntax with
  | some typeSyntax =>
    -- Elaborate the declared type signature with implicit quantification
    let declaredType ← TCM.recoverWithM
      (elaborateFunctionType typeSyntax)
      (TCM.typePlaceholder span)
    -- Split declared signature into:
    --   1) telescope prefix needed to check this function's term parameters
    --   2) remaining result type outside that prefix
    let (allParams, resultType) ← TCM.recoverWith
      (extractSignaturePrefix declaredType fn.params.size)
      (#[], declaredType)
    -- Extend context with prefix binders and check body against the exact remaining result type
    let (generatedParams, typedBody) ← withSignaturePrefixBindings allParams fn.params span do
      TCM.infallible (Soma.Dependent.checkSyntax fn.body resultType) default
    -- Solve pending instance constraints before zonking
    Soma.Dependent.solvePendingInstancesOrFail
    -- Zonk all solved metas so downstream passes see concrete types
    let declaredType' ← zonkValue declaredType
    reportUnsolvedMetas declaredType' span
    let typedBody' ← zonkExpr typedBody
    -- Resolve dangling bvar references to erased type params in fvar type annotations
    let mut erasedParams : Array (Nat × String) := #[]
    for i in [:allParams.size] do
      let (name, _, binder, _) := allParams[i]!
      let isErased := match binder with
        | .implicit | .strictImplicit => true
        | _ => false
      if isErased then
        erasedParams := erasedParams.push (i, name)
    let typedBody'' := if erasedParams.isEmpty then typedBody'
      else resolveErasedTypeBvars typedBody' allParams.size erasedParams
    -- Expand parameterized type abbreviations so downstream passes see real types
    let declaredType'' ← expandAbbrevValue declaredType'
    return (declaredType'', typedBody'', generatedParams)
  | none =>
    -- No signature: create fresh metavariables for param types
    let paramTypes ← fn.params.mapM fun _ => TCM.freshMetaVal (.vType .zero)
    -- Extend context with parameters and infer body type
    let (generatedParams, (inferredType, typedBody)) ← withFunctionParams fn.params paramTypes span do
      TCM.infallibleExpr (Soma.Dependent.inferSyntax fn.body) span
    -- Solve pending instance constraints before zonking
    Soma.Dependent.solvePendingInstancesOrFail
    -- Zonk all solved metas so downstream passes see concrete types
    let inferredType' ← zonkValue inferredType
    reportUnsolvedMetas inferredType' span
    let typedBody' ← zonkExpr typedBody
    -- Expand parameterized type abbreviations so downstream passes see real types
    let inferredType'' ← expandAbbrevValue inferredType'
    return (inferredType'', typedBody', generatedParams)

/-- Elaborate a constructor type: fields -> DataType params -/
def elaborateCtorType (typeName : Soma.Core.QualifiedName) (typeVarNames : Array String)
    (fieldTypeSyntax : Array Syntax.TypeExpr) : TCM Value := do
  -- Create an elaboration environment with type variables
  let mut elabEnv := Elaborate.ElabEnv.empty
  let mut typeVarVals : Array Value := #[]

  -- Bind type parameters as implicit forall variables
  for varName in typeVarNames do
    let varVal := Value.vNeutral (.vType .zero) (.nVar ⟨varName, ⟨elabEnv.level⟩⟩)
    typeVarVals := typeVarVals.push varVal
    elabEnv := elabEnv.extend varName (.vType .zero)

  let unique := typeName.id

  -- Build the result type: DataType applied to type vars
  let resultType := Value.vDataType unique typeVarVals.toList

  -- Elaborate field types and build function type
  let mut ctorType := resultType
  for fieldTySyntax in fieldTypeSyntax.reverse do
    let fieldTy ← Elaborate.elaborateType elabEnv fieldTySyntax
    -- Field arrows are non-dependent (the "_" parameter isn't referenced in ctorType),
    -- but ctorType may reference outer type variables. If we're inside type param scope,
    -- we need dependent closures to allow substitution of outer vars.
    if elabEnv.level > 0 then
      let codClosure ← Elaborate.mkDependentClosure "_" ctorType elabEnv
      ctorType := Value.vPi .omega .explicit "_" fieldTy codClosure
    else
      let codClosure ← Elaborate.mkConstClosure "_" ctorType
      ctorType := Value.vPi .omega .explicit "_" fieldTy codClosure

  -- Wrap in implicit foralls for type parameters: forall {a}. ... -> Maybe a
  -- These are dependent since the codomain references the bound type variable.
  for varName in typeVarNames.reverse do
    -- Pop the current variable from elabEnv to get the outer environment
    -- The closure should capture the OUTER environment (without the current var)
    let outerEnv : Elaborate.ElabEnv := {
      tyVars := elabEnv.tyVars.tail!
      level := elabEnv.level - 1
    }
    let codClosure ← Elaborate.mkDependentClosure varName ctorType outerEnv
    ctorType := Value.vPi .omega .implicit varName (.vType .zero) codClosure
    elabEnv := outerEnv

  return ctorType

/-- Elaborate an indexed constructor type from a full signature -/
def elaborateIndexedCtorType (_typeName : Soma.Core.QualifiedName) (_typeVarNames : Array String)
    (sigSyntax : Syntax.TypeExpr) : TCM Value := do
  -- Find ALL free type variables in the constructor signature
  -- This includes variables that may not be in the data type's parameter list
  let freeVarNames := sigSyntax.freeVars.map (·.name)
  let freeVarNamesUnique := freeVarNames.toList.eraseDups

  -- Create an elaboration environment with ALL free type variables
  let mut elabEnv := Elaborate.ElabEnv.empty

  -- Bind all free variables from the signature
  for varName in freeVarNamesUnique do
    elabEnv := elabEnv.extend varName (.vType .zero)

  -- Elaborate the full signature (e.g., `a -> Vec m a -> Vec (Succ m) a`)
  let ctorBodyType ← Elaborate.elaborateType elabEnv sigSyntax

  -- Wrap in implicit foralls for ALL free type variables
  let mut ctorType := ctorBodyType
  for varName in freeVarNamesUnique.reverse do
    let outerEnv : Elaborate.ElabEnv := {
      tyVars := elabEnv.tyVars.tail!
      level := elabEnv.level - 1
    }
    let codClosure ← Elaborate.mkDependentClosure varName ctorType outerEnv
    ctorType := Value.vPi .omega .implicit varName (.vType .zero) codClosure
    elabEnv := outerEnv

  return ctorType

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
    | .algebraic attrs typeName _ ctors _ =>
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
      | some k => Elaborate.elaborateType Elaborate.ElabEnv.empty k
      | none => pure (Value.vType Level.zero)
    paramKinds := paramKinds.push (param.name.name, kind)

  let mut classHeadTy : Value := Value.vType Level.zero
  for (paramName, paramKind) in paramKinds.reverse do
    let codClosure ← Elaborate.mkConstClosure paramName classHeadTy
    classHeadTy := Value.vPi .omega .implicit paramName paramKind codClosure
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
    value := none
    isConstructor := false
    origin := .typeDecl
  }
  g := g.register ns classNameStr classInfo
  return g

/-- Pre-register all type names from a module -/
def preRegisterTypes (module : Soma.Core.UntypedModule) : TCM Globals := do
  let ctx ← TCM.getCtx
  let ns := ctx.currentNamespace
  let mut globals := ctx.globals
  for typeDef in module.types do
    match typeDef with
    | .algebraic _ typeName typeVarNames _ _ =>
      let typeQN := typeName
      globals := globals.registerInductive typeQN .algebraic typeVarNames
      let dataTypeInfo : GlobalInfo := {
        name := typeQN
        type := Value.typeConstructorKind typeVarNames.size
        value := some (Value.vDataType typeQN.id [])
        isConstructor := false
        origin := .typeDecl
      }
      globals := globals.register ns typeName.display dataTypeInfo
    | .record _ recordName typeVarNames _ fields _ =>
      let typeQN := recordName
      globals := globals.registerInductive typeQN .record typeVarNames
        (fields.filterMap (·.1))
      let dataTypeInfo : GlobalInfo := {
        name := typeQN
        type := Value.typeConstructorKind typeVarNames.size
        value := some (Value.vDataType typeQN.id [])
        isConstructor := false
        origin := .typeDecl
      }
      globals := globals.register ns recordName.display dataTypeInfo
  return globals

def buildGlobals (module : Soma.Core.UntypedModule) : TCM Globals := do
  let ctx ← TCM.getCtx
  let ns := ctx.currentNamespace
  let mut globals := ctx.globals

  -- First pass: Register all data types
  for typeDef in module.types do
    match typeDef with
    | .algebraic _ typeName typeVarNames _ _ =>
      let typeQN := typeName
      globals := globals.registerInductive typeQN .algebraic typeVarNames
      let dataTypeInfo : GlobalInfo := {
        name := typeQN
        type := Value.typeConstructorKind typeVarNames.size
        value := some (Value.vDataType typeQN.id [])
        isConstructor := false
        origin := .typeDecl
      }
      globals := globals.register ns typeName.display dataTypeInfo
    | .record _ recordName typeVarNames _ fields _ =>
      let typeQN := recordName
      globals := globals.registerInductive typeQN .record typeVarNames
        (fields.filterMap (·.1))
      let dataTypeInfo : GlobalInfo := {
        name := typeQN
        type := Value.typeConstructorKind typeVarNames.size
        value := some (Value.vDataType typeQN.id [])
        isConstructor := false
        origin := .typeDecl
      }
      globals := globals.register ns recordName.display dataTypeInfo

  -- Second pass: Register constructors under their parent type namespace
  for typeDef in module.types do
    match typeDef with
    | .algebraic _ typeName typeVarNames constructors _ =>
      let typeNs := ns.push typeName.display
      for ctor in constructors do
        let ctorType ← TCM.recoverWithM
          (match ctor.sigSyntax with
            | some sig =>
              TCM.withGlobals globals (elaborateIndexedCtorType typeName typeVarNames sig)
            | none =>
              TCM.withGlobals globals (elaborateCtorType typeName typeVarNames ctor.fieldTypeSyntax))
          (TCM.typePlaceholder Span.uninhabited)
        let ctorSimpleName := ctor.name.id.original
        let info : GlobalInfo := {
          name := ctor.name
          type := ctorType
          value := none
          isConstructor := true
          ctorTag := ctor.tag
          origin := .constructor
        }
        globals := globals.register typeNs ctorSimpleName info
        globals := globals.registerConstructorMeta typeName {
          name := ctor.name
          simpleName := ctorSimpleName
          tag := ctor.tag
          arity := ctor.fieldTypeSyntax.size
          type := ctorType
        }
    | .record _ recordName typeVarNames ctorName fields _ =>
      let typeNs := ns.push recordName.display
      let ctorType ← TCM.recoverWithM
        (TCM.withGlobals globals (elaborateCtorType recordName typeVarNames (fields.map (·.2))))
        (TCM.typePlaceholder Span.uninhabited)
      let ctorInfo : GlobalInfo := {
        name := ctorName
        type := ctorType
        value := none
        isConstructor := true
        ctorTag := 0
        origin := .constructor
      }
      globals := globals.register typeNs "New" ctorInfo
      globals := globals.registerConstructorMeta recordName {
        name := ctorName
        simpleName := "New"
        tag := 0
        arity := fields.size
        type := ctorType
      }
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
          globals := globals.register typeNs fieldName accessorInfo

  for typeDef in module.types do
    match typeDef with
    | .algebraic _ typeName _ _ typeSpan =>
      match globals.lookupInductive typeName with
      | some indMeta =>
        let ctorTypes := indMeta.ctors.map (·.type)
        match Totality.checkDataTypePositivity typeName.id ctorTypes typeSpan with
        | .ok => pure ()
        | .violated reason violationSpan =>
          -- Prefer the positivity check's own violation span (pointing at the negative occurrence)
          let reportSpan :=
            if violationSpan == Span.uninhabited then typeSpan else violationSpan
          TCM.addError (.positivityViolation typeName.display reason reportSpan none)
      | none => pure ()
    | .record _ _ _ _ _ _ => pure ()

  -- Register type class heads as globals
  for typeClass in module.typeClasses do
    globals ← registerTypeClassHead globals typeClass none true

  for typeClass in module.typeClasses do
    let classNameStr := typeClass.name.display
    let classNs := ns.push classNameStr
    let methodFieldNames := typeClass.methodSignatures.map (·.1.display)
    let typeVarNames := typeClass.params.map (·.name.name)
    if let some classQN := globals.resolve ns #[] classNameStr then
      globals := globals.registerInductive classQN .record typeVarNames methodFieldNames
      let methodTypes := typeClass.methodSignatures.map (·.2)
      let ctorType ← TCM.recoverWithM
        (TCM.withGlobals globals (elaborateCtorType typeClass.name typeVarNames methodTypes))
        (TCM.typePlaceholder typeClass.span)
      let ctorUnique ← TCM.freshUnique "New"
      let ctorCoreName : Soma.Core.QualifiedName := ⟨ctorUnique⟩
      let ctorInfo : GlobalInfo := {
        name := ctorCoreName
        type := ctorType
        value := none
        isConstructor := true
        ctorTag := 0
        origin := .constructor
      }
      globals := globals.register classNs "New" ctorInfo
      globals := globals.registerConstructorMeta classQN {
        name := ctorCoreName
        simpleName := "New"
        tag := 0
        arity := methodTypes.size
        type := ctorType
      }
      for (methodName, _) in typeClass.methodSignatures do
        let fieldName := methodName.display
        let accessorUnique ← TCM.freshUnique fieldName
        let accessorType ← TCM.freshMetaVal (.vType .zero)
        let accessorInfo : GlobalInfo := {
          name := ⟨accessorUnique⟩
          type := accessorType
          value := none
          isConstructor := false
          origin := .projection
        }
        globals := globals.register classNs fieldName accessorInfo

  -- Register type class methods as globals (with error recovery for each method)
  for typeClass in module.typeClasses do
    for (methodName, methodTypeSyntax) in typeClass.methodSignatures do
      let methodType ← TCM.recoverWithM
        (do
          -- Elaborate kinds for each parameter
          let mut paramKinds : Array (String × Value) := #[]
          for param in typeClass.params do
            let kind ← match param.kind with
              | some k => Elaborate.elaborateType Elaborate.ElabEnv.empty k
              | none => pure (Value.vType Level.zero)
            paramKinds := paramKinds.push (param.name.name, kind)

          -- Collect free type variables from the method signature that are not trait params
          let traitParamNames := paramKinds.map (·.1)
          let methodFreeVars := methodTypeSyntax.freeVars.map (·.name)
          let methodOwnVars := methodFreeVars.filter (fun v => !traitParamNames.contains v)
          let methodOwnVarsUnique := methodOwnVars.toList.eraseDups

          -- Build an elaboration environment with:
          -- 1. Method's own free type variables (innermost, bound first)
          -- 2. Trait's type parameters (outermost)
          let mut elabEnv := Elaborate.ElabEnv.empty

          -- First, add method's own type variables
          for varName in methodOwnVarsUnique do
            elabEnv := elabEnv.extend varName (.vType .zero)

          -- Then, add trait's type parameters
          for (paramName, kind) in paramKinds do
            elabEnv := elabEnv.extend paramName kind

          -- Elaborate the method type signature with all type params in scope
          let methodTypeBody ← TCM.withGlobals globals (Elaborate.elaborateType elabEnv methodTypeSyntax)

          -- Wrap in implicit foralls for method's own type variables (right to left)
          let mut methodType := methodTypeBody

          let classNameStr' := typeClass.name.display
          if let some classQN := globals.resolve ns #[] classNameStr' then
            let methodOwnVarCount := methodOwnVarsUnique.length
            let mut typeParamVars : List Value := []
            let mut paramIdx := 0
            for (paramName, paramKind) in paramKinds do
              let paramLevel := methodOwnVarCount + paramIdx
              typeParamVars := typeParamVars ++ [Value.vNeutral paramKind (.nVar ⟨paramName, ⟨paramLevel⟩⟩)]
              paramIdx := paramIdx + 1
            let instanceDomain := Value.vDataType classQN.id typeParamVars
            let codClosure ← Elaborate.mkDependentClosure "$dict" methodType elabEnv
            methodType := Value.vPi .omega .instance_ "$dict" instanceDomain codClosure

          let mut outerEnv := elabEnv

          -- First wrap trait parameters (outermost foralls)
          for (paramName, paramKind) in paramKinds.reverse do
            outerEnv := {
              tyVars := outerEnv.tyVars.tail!
              level := outerEnv.level - 1
            }
            let codClosure ← Elaborate.mkDependentClosure paramName methodType outerEnv
            methodType := Value.vPi .omega .implicit paramName paramKind codClosure

          -- Then wrap method's own type variables (innermost foralls, but still implicit)
          for varName in methodOwnVarsUnique.reverse do
            outerEnv := {
              tyVars := outerEnv.tyVars.tail!
              level := outerEnv.level - 1
            }
            let codClosure ← Elaborate.mkDependentClosure varName methodType outerEnv
            methodType := Value.vPi .omega .implicit varName (.vType .zero) codClosure

          return methodType)
        (TCM.typePlaceholder typeClass.span)

      let methodInfo : GlobalInfo := {
        name := methodName
        type := methodType
        value := none
        isConstructor := false
        origin := .traitMethod
      }
      globals := globals.register ns methodName.display methodInfo

  -- Register all functions (after data types so function signatures can reference them)
  for fn in module.functions do
    let fnType ← TCM.recoverWithM
      (match fn.declaredTypeSyntax with
        | some typeSyntax => TCM.withGlobals globals (elaborateFunctionType typeSyntax)
        | none => TCM.freshMetaVal (.vType .zero))
      (TCM.typePlaceholder fn.span)
    let intrinsic ← TCM.recoverWithM (inferIntrinsicInfo fn) (pure none)
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
    globals := globals.register ns fn.name.display info

  globals ← indexWiredRoles module globals

  return globals

/-- Build the InstanceEnv from module type classes and instances -/
def buildInstanceEnv (module : Soma.Core.UntypedModule) (_moduleName : String)
    : TCM (InstanceEnv × TraitElaborate.InstanceMap × Array Soma.Core.TypedFunction) := do
  TraitElaborate.buildInstanceEnvFromModule module

/-- Build the InstanceEnv incrementally, reusing cached info for unchanged definitions -/
def buildInstanceEnvIncremental
  (module : Soma.Core.UntypedModule)
    (_moduleName : String)
    (prevEnv : InstanceEnv)
    (prevInstanceMap : TraitElaborate.InstanceMap)
    (dirtyNames : Std.HashSet String)
    : TCM (InstanceEnv × TraitElaborate.InstanceMap × Array Soma.Core.TypedFunction) := do
  TraitElaborate.buildInstanceEnvFromModuleIncremental module prevEnv prevInstanceMap dirtyNames

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
    let expansion ← Elaborate.elaborateType Elaborate.ElabEnv.empty typeAbbrev.expansion
    return { abbrevId := abbrevUnique, arity := 0, expansion, span := typeAbbrev.span }
  else
    -- Parameterized: build environment with type parameters
    let mut elabEnv := Elaborate.ElabEnv.empty
    for paramName in typeAbbrev.params do
      elabEnv := elabEnv.extend paramName (Value.vType Level.zero)

    -- Elaborate the expansion body in the parameter context
    let bodyVal ← Elaborate.elaborateType elabEnv typeAbbrev.expansion

    -- Build a proper dependent closure that substitutes parameters when applied
    let numParams := typeAbbrev.params.size
    let bodyExpr := Soma.Core.quoteExpr ⟨numParams⟩ bodyVal

    -- Wrap all params except the outermost (first) in nested Expr.pi from inside out
    let mut innerExpr := bodyExpr
    for i in List.range (numParams - 1) |>.reverse do
      let paramIdx := i + 1
      let paramName := typeAbbrev.params[paramIdx]!
      innerExpr := Soma.Core.Expr.pi .omega .explicit paramName (Soma.Core.Expr.sort Level.zero) innerExpr

    -- Create the outermost closure with empty env
    let outerName := typeAbbrev.params[0]!
    let closure := Soma.Core.Closure.term outerName (Soma.Core.Env.mk [] 0) innerExpr
    let expansion := Value.vLam outerName closure

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
    (nameStr : String)
    (kind : InductiveKind)
    (typeVarNames : Array String := #[])
    (fieldNames : Array String := #[])
    (prevGlobals : Option Globals)
    (isDirty : Bool)
    : TCM Globals := do
  let ns ← TCM.getCurrentNamespace
  if !isDirty then
    if let some prev := prevGlobals then
      if let some prevQN := prev.resolve ns #[] nameStr then
        if let some info := prev.getDef prevQN then
          let mut g := globals.register ns nameStr info
          g := g.registerInductive prevQN kind typeVarNames fieldNames
          return g

  let typeUnique ← TCM.freshUnique nameStr
  let typeQN : Soma.Core.QualifiedName := ⟨typeUnique⟩
  let mut g := globals.registerInductive typeQN kind typeVarNames fieldNames
  let dataTypeInfo : GlobalInfo := {
    name := typeQN
    type := Value.vType .zero
    value := some (Value.vDataType typeUnique [])
    isConstructor := false
    origin := .typeDecl
  }
  return g.register ns nameStr dataTypeInfo

/-- Core constructor registration logic -/
private def registerConstructorRaw
    (globals : Globals)
    (typeName : Soma.Core.QualifiedName)
    (typeVarNames : Array String)
    (ctorSimpleName : String)
    (ctorTag : Nat)
    (fieldTypes : Array Syntax.TypeExpr)
    (sigSyntax : Option Syntax.TypeExpr)
    (prevGlobals : Option Globals)
    (isDirty : Bool)
    : TCM Globals := do
  let ns ← TCM.getCurrentNamespace
  let typeNs := ns.push typeName.display

  if !isDirty then
    if let some prev := prevGlobals then
      if let some ctorQN := prev.resolve ns #[typeName.display] ctorSimpleName then
        if let some info := prev.getDef ctorQN then
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
      | none => TCM.withGlobals globals (elaborateCtorType typeName typeVarNames fieldTypes))
    (TCM.typePlaceholder Span.uninhabited)
  let ctorUnique ← TCM.freshUnique ctorSimpleName
  let info : GlobalInfo := {
    name := ⟨ctorUnique⟩
    type := ctorType
    value := none
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
    (typeVarNames : Array String)
  (ctor : Soma.Core.UntypedConstructor)
    (prevGlobals : Option Globals)
    (isDirty : Bool)
    : TCM Globals :=
  registerConstructorRaw globals typeName typeVarNames
    ctor.name.id.original ctor.tag ctor.fieldTypeSyntax ctor.sigSyntax
    prevGlobals isDirty

/-- Register or reuse record field accessors, returns updated globals -/
private def registerRecordFieldAccessors
    (globals : Globals)
    (recordName : Soma.Core.QualifiedName)
    (fields : Array (Option String × Syntax.TypeExpr))
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
    (typeVarNames : Array String)
    (_ctorName : Soma.Core.QualifiedName)
    (fields : Array (Option String × Syntax.TypeExpr))
    (prevGlobals : Option Globals)
    (isDirty : Bool)
    : TCM Globals := do
  let g ← registerConstructorRaw globals recordName typeVarNames
    "New" 0 (fields.map (·.2)) none prevGlobals isDirty
  registerRecordFieldAccessors g recordName fields prevGlobals isDirty

/-- Elaborate a type class method type -/
private def elaborateMethodType
    (globals : Globals)
  (typeClass : Soma.Core.TypeClassMeta)
    (methodTypeSyntax : Syntax.TypeExpr)
    : TCM Value := do
  -- Elaborate kinds for each parameter
  let mut paramKinds : Array (String × Value) := #[]
  for param in typeClass.params do
    let kind ← match param.kind with
      | some k => Elaborate.elaborateType Elaborate.ElabEnv.empty k
      | none => pure (Value.vType Level.zero)
    paramKinds := paramKinds.push (param.name.name, kind)

  let mut elabEnv := Elaborate.ElabEnv.empty
  for (paramName, kind) in paramKinds do
    elabEnv := elabEnv.extend paramName kind
  let methodTypeBody ← TCM.withGlobals globals (Elaborate.elaborateType elabEnv methodTypeSyntax)
  let mut methodType := methodTypeBody

  let classNameStr' := typeClass.name.display
  if let some classQN := globals.resolve #[] #[] classNameStr' then
    let mut typeParamVars : List Value := []
    let mut paramIdx := 0
    for (paramName, paramKind) in paramKinds do
      typeParamVars := typeParamVars ++ [Value.vNeutral paramKind (.nVar ⟨paramName, ⟨paramIdx⟩⟩)]
      paramIdx := paramIdx + 1
    let instanceDomain := Value.vDataType classQN.id typeParamVars
    let codClosure ← Elaborate.mkDependentClosure "$dict" methodType elabEnv
    methodType := Value.vPi .omega .instance_ "$dict" instanceDomain codClosure

  let mut outerEnv := elabEnv
  for (paramName, paramKind) in paramKinds.reverse do
    outerEnv := { tyVars := outerEnv.tyVars.tail!, level := outerEnv.level - 1 }
    let codClosure ← Elaborate.mkDependentClosure paramName methodType outerEnv
    methodType := Value.vPi .omega .implicit paramName paramKind codClosure
  return methodType

/-- Register or reuse a type class method, returns updated globals -/
private def registerMethod
    (globals : Globals)
  (typeClass : Soma.Core.TypeClassMeta)
  (methodName : Soma.Core.QualifiedName)
    (methodTypeSyntax : Syntax.TypeExpr)
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
  let methodUnique ← TCM.freshUnique methodName.display
  let methodInfo : GlobalInfo := {
    name := ⟨methodUnique⟩
    type := methodType
    value := none
    isConstructor := false
    origin := .traitMethod
  }
  return globals.register ns methodName.display methodInfo

/-- Register or reuse a function, returns updated globals -/
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

/-- Build a Globals environment incrementally, reusing cached types for unchanged definitions -/
def buildGlobalsIncremental
  (module : Soma.Core.UntypedModule)
    (prevGlobals : Globals)
    (dirtyNames : Std.HashSet String)
    : TCM Globals := do
  let ctx ← TCM.getCtx
  let mut globals := ctx.globals

  -- First pass: Register all data types
  for typeDef in module.types do
    match typeDef with
    | .algebraic _ typeName typeVarNames _ _ =>
      let nameStr := typeName.display
      let isDirty := dirtyNames.contains nameStr
      globals ← registerDataType globals nameStr .algebraic typeVarNames #[] (some prevGlobals) isDirty
    | .record _ recordName typeVarNames _ fields _ =>
      let nameStr := recordName.display
      let isDirty := dirtyNames.contains nameStr
      globals ← registerDataType globals nameStr .record typeVarNames (fields.filterMap (·.1)) (some prevGlobals) isDirty

  -- Second pass: Register constructors
  for typeDef in module.types do
    match typeDef with
    | .algebraic _ typeName typeVarNames constructors _ =>
      let isDirty := dirtyNames.contains typeName.display
      for ctor in constructors do
        globals ← registerConstructor globals typeName typeVarNames ctor (some prevGlobals) isDirty
    | .record _ recordName typeVarNames ctorName fields _ =>
      let isDirty := dirtyNames.contains recordName.display
      globals ← registerRecordConstructor globals recordName typeVarNames ctorName fields (some prevGlobals) isDirty

  -- Register type class heads
  for typeClass in module.typeClasses do
    let isDirty := dirtyNames.contains typeClass.name.display
    globals ← registerTypeClassHead globals typeClass (some prevGlobals) isDirty

  for typeClass in module.typeClasses do
    let classNameStr := typeClass.name.display
    let isDirty := dirtyNames.contains classNameStr
    let methodFieldNames := typeClass.methodSignatures.map (·.1.display)
    let typeVarNames := typeClass.params.map (·.name.name)
    let ns ← TCM.getCurrentNamespace
    if let some classQN := globals.resolve ns #[] classNameStr then
      if !isDirty then
        if let some prevQN := prevGlobals.resolve ns #[] classNameStr then
          if let some indInfo := prevGlobals.lookupInductive prevQN then
            globals := { globals with inductives := globals.inductives.insert classQN indInfo }
          else
            globals := globals.registerInductive classQN .record typeVarNames methodFieldNames
        else
          globals := globals.registerInductive classQN .record typeVarNames methodFieldNames
      else
        globals := globals.registerInductive classQN .record typeVarNames methodFieldNames
      let fields := typeClass.methodSignatures.map (fun (name, ty) => (some name.display, ty))
      globals ← registerRecordConstructor globals typeClass.name typeVarNames typeClass.name fields (some prevGlobals) isDirty

  -- Register type class methods
  for typeClass in module.typeClasses do
    let isDirty := dirtyNames.contains typeClass.name.display
    for (methodName, methodTypeSyntax) in typeClass.methodSignatures do
      globals ← registerMethod globals typeClass methodName methodTypeSyntax (some prevGlobals) isDirty

  -- Register all functions
  for fn in module.functions do
    let isDirty := dirtyNames.contains fn.name.display
    globals ← registerFunction globals fn (some prevGlobals) isDirty

  globals ← indexWiredRoles module globals

  return globals

end Soma.Dependent.Driver
