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

private def inferIntrinsicInfo (fn : Soma.Core.UntypedFunction) : Option Intrinsic :=
  if fn.attrs.intrinsic then
    match PrimOp.fromString? fn.name.display with
    | some op => some (.primOp op)
    | none =>
      match FFIOp.fromString? fn.name.display with
      | some op => some (.ffiOp op)
      | none => some (.extern (fn.attrs.extern.getD fn.name.display))
  else
    fn.attrs.extern.map Intrinsic.extern

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

/-- Check positivity for a data type definition -/
def checkDataTypePositivity (typeDef : Soma.Core.UntypedTypeDef) (ctx : TCContext) (state : TCState)
    : Array TCError :=
  match typeDef with
  | .algebraic _ name _params constructors =>
    -- Look up the registered Unique, or create a placeholder
    let typeName := name.display
    let unique : Soma.Unique := match ctx.globals.lookupUnique typeName with
      | some id => id
      | none => ⟨state.uniqueSupply.nextId, state.uniqueSupply.module, typeName⟩

    -- Elaborate each constructor's field types
    let ctorTypes := constructors.foldl (init := #[]) fun acc ctor =>
      ctor.fieldTypeSyntax.foldl (init := acc) fun acc2 fieldTyExpr =>
        match (Elaborate.elaborateType Elaborate.ElabEnv.empty fieldTyExpr).run ctx state with
        | .ok (fieldVal, _) => acc2.push fieldVal
        | .error _ => acc2  -- Skip fields that fail to elaborate

    -- Run positivity check
    match Totality.checkDataTypePositivity unique ctorTypes Span.uninhabited with
    | .ok => #[]
    | .violated reason violationSpan =>
      #[TCError.positivityViolation typeName reason violationSpan none]

  | .record _ _ _ _ _ =>
    -- Records are always positive
    #[]

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

/-- Extract a binder telescope prefix from a Pi type -/
partial def extractSignaturePrefix (ty : Value) (numExplicit : Nat)
    : TCM (Array (String × Value × Soma.Core.BinderInfo) × Value) := do
  let ty' ← force ty
  match ty' with
  | .vPi _qty binder name dom cod =>
    -- Once we consumed all explicit term parameters, stop before the next explicit binder
    if numExplicit == 0 && !binder.isImplicit then
      return (#[], ty')
    let lvl ← TCM.currentLevel
    let dummyArg := Value.vNeutral dom (.nVar ⟨name, lvl⟩)
    let codTy ← applyClosure cod dummyArg
    let remainingExplicit := if binder.isImplicit then numExplicit else numExplicit - 1
    let (restParams, resultTy) ← extractSignaturePrefix codTy remainingExplicit
    return (#[(name, dom, binder)] ++ restParams, resultTy)
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
  Returns generated Unique×String pairs for those explicit term parameters. -/
def withSignaturePrefixBindings (allParams : Array (String × Value × Soma.Core.BinderInfo))
    (explicitParams : Array String)
    (span : Span) (action : TCM α) : TCM (Array (Soma.Unique × String) × α) := do
  -- Pre-generate all local ids to collect them
  let mut explicitBindings : Array (Soma.Unique × String) := #[]
  let mut allBindings : Array (Soma.Unique × String × Soma.Core.BinderInfo) := #[]
  let mut eIdx : Nat := 0
  for (name, _, binder) in allParams do
    if binder.isImplicit then
      let bindingId ← TCM.freshLocalId name
      allBindings := allBindings.push (bindingId, name, binder)
    else
      let paramName := if h : eIdx < explicitParams.size then explicitParams[eIdx] else name
      let bindingId ← TCM.freshLocalId paramName
      allBindings := allBindings.push (bindingId, paramName, .explicit)
      explicitBindings := explicitBindings.push (bindingId, paramName)
      eIdx := eIdx + 1
  -- Now bind them all
  let rec go (idx : Nat) : TCM α := do
    if idx >= allBindings.size then
      action
    else
      let (bindingId, paramName, binder) := allBindings[idx]!
      let (_, ty, _) := allParams[idx]!
      TCM.withBinding paramName bindingId ty .omega binder span do
        go (idx + 1)
  let result ← go 0
  return (explicitBindings, result)

/-- Type check a single function using dependent types.
    Returns (fnType, typedBody, generatedParams) where generatedParams contains local ids. -/
def checkFunction (fn : Soma.Core.UntypedFunction)
  : TCM (Value × Soma.Core.Expr × Array (Soma.Unique × String)) := do
  let span := fn.span
  -- Intrinsic/extern functions have no real body — just elaborate the type
  if fn.attrs.intrinsic || fn.attrs.extern.isSome then
    match fn.declaredTypeSyntax with
    | some typeSyntax =>
      let declaredType ← TCM.recoverWithM
        (Elaborate.elaborateType Elaborate.ElabEnv.empty typeSyntax)
        (TCM.typePlaceholder span)
      let placeholderBody := Soma.Core.Expr.lit (.string s!"placeholder:{fn.name.display}")
      return (declaredType, placeholderBody, #[])
    | none =>
      let ty ← TCM.freshMetaVal (.vType .zero)
      let placeholderBody := Soma.Core.Expr.lit (.string s!"placeholder:{fn.name.display}")
      return (ty, placeholderBody, #[])
  match fn.declaredTypeSyntax with
  | some typeSyntax =>
    -- Elaborate the declared type signature
    let declaredType ← TCM.recoverWithM
      (Elaborate.elaborateType Elaborate.ElabEnv.empty typeSyntax)
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
    -- Zonk all solved metas so downstream passes see concrete types
    let declaredType' ← zonkValue declaredType
    let typedBody' ← zonkExpr typedBody
    return (declaredType', typedBody', generatedParams)
  | none =>
    -- No signature: create fresh metavariables for param types
    let paramTypes ← fn.params.mapM fun _ => TCM.freshMetaVal (.vType .zero)
    -- Extend context with parameters and infer body type
    let (generatedParams, (inferredType, typedBody)) ← withFunctionParams fn.params paramTypes span do
      TCM.infallibleExpr (Soma.Dependent.inferSyntax fn.body) span
    -- Zonk all solved metas so downstream passes see concrete types
    let inferredType' ← zonkValue inferredType
    let typedBody' ← zonkExpr typedBody
    return (inferredType', typedBody', generatedParams)

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

  -- Look up the registered Unique, or create a fresh one if not found
  let unique ← match ← TCM.lookupUnique typeName.display with
    | some id => pure id
    | none => TCM.freshUnique typeName.display

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
  let freeVarNames := sigSyntax.freeVars.map (·.value)
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

/-- Elaborate a function type signature, properly handling free type variables.
    Free type variables in the signature become implicit forall-bound parameters.
    For example, `a -> [a] -> [a]` becomes `forall {a : Type}. a -> [a] -> [a]` -/
def elaborateFunctionType (sigSyntax : Syntax.TypeExpr) : TCM Value := do
  -- Find all free type variables in the function signature
  let freeVarNames := sigSyntax.freeVars.map (·.value)
  let freeVarNamesUnique := freeVarNames.toList.eraseDups

  -- Create an elaboration environment with all free type variables bound
  let mut elabEnv := Elaborate.ElabEnv.empty

  -- Bind all free variables from the signature
  for varName in freeVarNamesUnique do
    elabEnv := elabEnv.extend varName (.vType .zero)

  -- Elaborate the function type body
  let fnBodyType ← Elaborate.elaborateType elabEnv sigSyntax

  -- Wrap in implicit foralls for all free type variables
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

private def registerWiredRoleFromAttrs
    (globals : Globals)
    (attrs : Array Syntax.Attribute)
    (info : GlobalInfo)
    (what : String)
    : TCM Globals := do
  let mut g := globals
  for attr in attrs do
    if attr.name.value == "wired_in" then
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
    | .algebraic attrs typeName _ ctors =>
      if let some typeInfo := g.lookup typeName.display then
        g ← registerWiredRoleFromAttrs g attrs typeInfo s!"type {typeName.display}"
      for ctor in ctors do
        let ctorQualifiedName := s!"{typeName.display}::{ctor.name.id.original}"
        if let some ctorInfo := g.lookup ctorQualifiedName then
          g ← registerWiredRoleFromAttrs g ctor.attrs ctorInfo s!"constructor {ctorQualifiedName}"
    | .record attrs recordName _ _ _ =>
      if let some typeInfo := g.lookup recordName.display then
        g ← registerWiredRoleFromAttrs g attrs typeInfo s!"type {recordName.display}"
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
    paramKinds := paramKinds.push (param.name.value, kind)

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

  if !isDirty then
    if let some prev := prevGlobals then
      if let some info := prev.lookup classNameStr then
        let mut g := globals.insert classNameStr info
        if let some classUnique := prev.lookupUnique classNameStr then
          g := g.registerUnique classNameStr classUnique
          TCM.registerUnique classNameStr classUnique
        return g

  let classUnique ← match globals.lookupUnique classNameStr with
    | some id => pure id
    | none => TCM.freshUnique classNameStr

  let mut g := globals.registerUnique classNameStr classUnique
  TCM.registerUnique classNameStr classUnique

  let classHeadTy ← TCM.recoverWithM
    (TCM.withGlobals g (elaborateTypeClassHeadType typeClass))
    (TCM.typePlaceholder typeClass.span)

  let classInfo : GlobalInfo := {
    name := ⟨classUnique⟩
    type := classHeadTy
    value := none
    isConstructor := false
    origin := .typeDecl
  }
  g := g.insert classNameStr classInfo
  return g

/-- Build a Globals enviro      -- Check for builtin higher-kinded types (List, Array, IO, Ref)
nment from all function definitions in a module -/
def buildGlobals (module : Soma.Core.UntypedModule) : TCM Globals := do
  -- Start with existing globals from context to preserve external uniques
  let ctx ← TCM.getCtx
  let mut globals := ctx.globals

  -- First pass: Register all data types (so they can be referenced by functions and constructors)
  for typeDef in module.types do
    match typeDef with
    | .algebraic _ typeName typeVarNames _ =>
      -- Generate a proper Unique for this data type
      let typeUnique ← TCM.freshUnique typeName.display
      -- Register the Unique in both local globals and TCM context
      globals := globals.registerUnique typeName.display typeUnique
      globals := globals.registerInductive typeName.display typeUnique .algebraic typeVarNames
      TCM.registerUnique typeName.display typeUnique

      -- Register the data type name itself (for evaluation of Expr.const)
      let dataTypeVal := Value.vDataType typeUnique []
      let dataTypeInfo : GlobalInfo := {
        name := ⟨typeUnique⟩
        type := Value.typeConstructorKind typeVarNames.size
        value := some dataTypeVal
        isConstructor := false
        origin := .typeDecl
      }
      globals := globals.insert typeName.display dataTypeInfo
    | .record _ recordName typeVarNames _ fields =>
      let typeUnique ← TCM.freshUnique recordName.display
      globals := globals.registerUnique recordName.display typeUnique
      globals := globals.registerInductive recordName.display typeUnique .record typeVarNames
        (fields.filterMap (·.1))
      TCM.registerUnique recordName.display typeUnique
      let dataTypeVal := Value.vDataType typeUnique []
      let dataTypeInfo : GlobalInfo := {
        name := ⟨typeUnique⟩
        type := Value.typeConstructorKind typeVarNames.size
        value := some dataTypeVal
        isConstructor := false
        origin := .typeDecl
      }
      globals := globals.insert recordName.display dataTypeInfo

  -- Second pass: Register constructors (now data types are available for reference)
  for typeDef in module.types do
    match typeDef with
    | .algebraic _ typeName typeVarNames constructors =>
      for ctor in constructors do
        -- Elaborate the constructor type by checking wheter indexed (has signature) or simple (has fields)
        -- Use withGlobals so the TCM context sees the registered data types
        let ctorType ← TCM.recoverWithM
          (match ctor.sigSyntax with
            | some sig =>
              -- Indexed constructor: elaborate full signature
              TCM.withGlobals globals (elaborateIndexedCtorType typeName typeVarNames sig)
            | none =>
              -- Simple constructor: build type from fields
              TCM.withGlobals globals (elaborateCtorType typeName typeVarNames ctor.fieldTypeSyntax))
          (TCM.typePlaceholder Span.uninhabited)
        -- Get the simple constructor name
        let ctorSimpleName := ctor.name.id.original
        let ctorQualifiedName := s!"{typeName.display}::{ctorSimpleName}"
        let ctorUnique ← TCM.freshUnique ctorQualifiedName
        let ctorCoreName : Soma.Core.QualifiedName := ⟨ctorUnique⟩
        let info : GlobalInfo := {
          name := ctorCoreName
          type := ctorType
          value := none
          isConstructor := true
          ctorTag := ctor.tag
          origin := .constructor
        }
        globals := globals.insert ctorQualifiedName info
        -- Register in child namespace: TypeName → CtorSimpleName
        globals := globals.insertInChild typeName.display ctorSimpleName info
        let ctorMeta : ConstructorMeta := {
          name := ctorCoreName
          simpleName := ctorSimpleName
          tag := ctor.tag
          arity := ctor.fieldTypeSyntax.size
          type := ctorType
        }
        globals := globals.registerConstructorMeta typeName.display ctorMeta
    | .record _ recordName typeVarNames _ctorName fields =>
      let ctorSimpleName := "New"
      let ctorQualifiedName := s!"{recordName.display}::{ctorSimpleName}"
      let ctorType ← TCM.recoverWithM
        (TCM.withGlobals globals (elaborateCtorType recordName typeVarNames (fields.map (·.2))))
        (TCM.typePlaceholder Span.uninhabited)
      let ctorUnique ← TCM.freshUnique ctorQualifiedName
      let ctorCoreName : Soma.Core.QualifiedName := ⟨ctorUnique⟩
      let info : GlobalInfo := {
        name := ctorCoreName
        type := ctorType
        value := none
        isConstructor := true
        ctorTag := 0
        origin := .constructor
      }
      globals := globals.insert ctorQualifiedName info
      globals := globals.insertInChild recordName.display ctorSimpleName info
      let ctorMeta : ConstructorMeta := {
        name := ctorCoreName
        simpleName := ctorSimpleName
        tag := 0
        arity := fields.size
        type := ctorType
      }
      globals := globals.registerConstructorMeta recordName.display ctorMeta
      for (fieldNameOpt, _) in fields do
        if let some fieldName := fieldNameOpt then
          let accessorNameStr := s!"{recordName.display}::{fieldName}"
          let accessorUnique ← TCM.freshUnique accessorNameStr
          let accessorType ← TCM.freshMetaVal (.vType .zero)
          let accessorInfo : GlobalInfo := {
            name := ⟨accessorUnique⟩
            type := accessorType
            value := none
            isConstructor := false
            origin := .projection
          }
          globals := globals.insert accessorNameStr accessorInfo
          globals := globals.insertInChild recordName.display fieldName accessorInfo

  -- Register type class heads as globals
  for typeClass in module.typeClasses do
    globals ← registerTypeClassHead globals typeClass none true

  for typeClass in module.typeClasses do
    let classNameStr := typeClass.name.display
    let methodFieldNames := typeClass.methodSignatures.map (·.1.display)
    let typeVarNames := typeClass.params.map (·.name.value)
    if let some classUnique := globals.lookupUnique classNameStr then
      globals := globals.registerInductive classNameStr classUnique .record typeVarNames methodFieldNames
      let methodTypes := typeClass.methodSignatures.map (·.2)
      let ctorSimpleName := "New"
      let ctorQualifiedName := s!"{classNameStr}::{ctorSimpleName}"
      let ctorType ← TCM.recoverWithM
        (TCM.withGlobals globals (elaborateCtorType typeClass.name typeVarNames methodTypes))
        (TCM.typePlaceholder typeClass.span)
      let ctorUnique ← TCM.freshUnique ctorQualifiedName
      let ctorCoreName : Soma.Core.QualifiedName := ⟨ctorUnique⟩
      let ctorInfo : GlobalInfo := {
        name := ctorCoreName
        type := ctorType
        value := none
        isConstructor := true
        ctorTag := 0
        origin := .constructor
      }
      globals := globals.insert ctorQualifiedName ctorInfo
      globals := globals.insertInChild classNameStr ctorSimpleName ctorInfo
      let ctorMeta : ConstructorMeta := {
        name := ctorCoreName
        simpleName := ctorSimpleName
        tag := 0
        arity := methodTypes.size
        type := ctorType
      }
      globals := globals.registerConstructorMeta classNameStr ctorMeta
      for (methodName, _) in typeClass.methodSignatures do
        let fieldName := methodName.display
        let accessorNameStr := s!"{classNameStr}::{fieldName}"
        let accessorUnique ← TCM.freshUnique accessorNameStr
        let accessorType ← TCM.freshMetaVal (.vType .zero)
        let accessorInfo : GlobalInfo := {
          name := ⟨accessorUnique⟩
          type := accessorType
          value := none
          isConstructor := false
          origin := .projection
        }
        globals := globals.insert accessorNameStr accessorInfo
        globals := globals.insertInChild classNameStr fieldName accessorInfo

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
            paramKinds := paramKinds.push (param.name.value, kind)

          -- Collect free type variables from the method signature that are not trait params
          let traitParamNames := paramKinds.map (·.1)
          let methodFreeVars := methodTypeSyntax.freeVars.map (·.value)
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

      let methodUnique ← TCM.freshUnique methodName.display
      let methodInfo : GlobalInfo := {
        name := ⟨methodUnique⟩
        type := methodType
        value := none
        isConstructor := false
        origin := .traitMethod
      }
      globals := globals.insert methodName.display methodInfo

  -- Register all functions (after data types so function signatures can reference them)
  for fn in module.functions do
    -- Elaborate the type signature if present, otherwise create a placeholder
    -- Use elaborateFunctionType to properly handle free type variables as implicit foralls
    let fnType ← TCM.recoverWithM
      (match fn.declaredTypeSyntax with
        | some typeSyntax => TCM.withGlobals globals (elaborateFunctionType typeSyntax)
        | none => TCM.freshMetaVal (.vType .zero))
      (TCM.typePlaceholder fn.span)
    let info : GlobalInfo := {
      name := fn.name
      type := fnType
      value := none
      intrinsic := inferIntrinsicInfo fn
      isConstructor := false
      origin := match inferIntrinsicInfo fn with
        | some (.extern _) => if fn.attrs.intrinsic then .intrinsic else .extern
        | some _ => .intrinsic
        | none => .function
    }
    globals := globals.insert fn.name.display info

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

    -- Wrap in Pi types (right to left) to create: forall p1 p2 ... pn. body
    let mut expansion := bodyVal
    for paramName in typeAbbrev.params.reverse do
      let closure ← TCM.mkConstClosure paramName expansion
      expansion := Value.vPi .omega .explicit paramName (Value.vType Level.zero) closure

    return { abbrevId := abbrevUnique, arity, expansion, span := typeAbbrev.span }

/-- Build the AbbrevEnv from module type abbreviations -/
def buildAbbrevEnv (module : Soma.Core.UntypedModule) : TCM AbbrevEnv := do
  let mut env := AbbrevEnv.empty
  for typeAbbrev in module.abbreviations do
    let info ← elaborateAbbrev typeAbbrev
    env := env.insert info
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
  -- Check if we can reuse from previous globals
  if !isDirty then
    if let some prev := prevGlobals then
      if let some info := prev.lookup nameStr then
        let mut g := globals.insert nameStr info
        if let some unique := prev.lookupUnique nameStr then
          g := g.registerUnique nameStr unique
          g := g.registerInductive nameStr unique kind typeVarNames fieldNames
          TCM.registerUnique nameStr unique
        else if let some metaInfo := prev.lookupInductive nameStr then
          g := { g with inductives := g.inductives.insert metaInfo.name metaInfo }
        return g

  -- Must elaborate fresh
  let typeUnique ← TCM.freshUnique nameStr
  let mut g := globals.registerUnique nameStr typeUnique
  g := g.registerInductive nameStr typeUnique kind typeVarNames fieldNames
  TCM.registerUnique nameStr typeUnique
  let dataTypeVal := Value.vDataType typeUnique []
  let dataTypeInfo : GlobalInfo := {
    name := ⟨typeUnique⟩
    type := Value.vType .zero
    value := some dataTypeVal
    isConstructor := false
    origin := .typeDecl
  }
  return g.insert nameStr dataTypeInfo

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
  let ctorQualifiedName := s!"{typeName.display}::{ctorSimpleName}"

  -- Check if we can reuse from previous globals
  if !isDirty then
    if let some prev := prevGlobals then
      if let some info := prev.lookup ctorQualifiedName then
        let mut g := globals.insert ctorQualifiedName info
        g := g.insertInChild typeName.display ctorSimpleName info
        let ctorMeta : ConstructorMeta := {
          name := info.name
          simpleName := ctorSimpleName
          tag := info.ctorTag
          arity := info.type.explicitArity
          type := info.type
        }
        g := g.registerConstructorMeta typeName.display ctorMeta
        if !g.contains ctorSimpleName then
          g := g.insert ctorSimpleName info
        return g

  -- Must elaborate fresh
  let ctorType ← TCM.recoverWithM
    (match sigSyntax with
      | some sig => TCM.withGlobals globals (elaborateIndexedCtorType typeName typeVarNames sig)
      | none => TCM.withGlobals globals (elaborateCtorType typeName typeVarNames fieldTypes))
    (TCM.typePlaceholder Span.uninhabited)
  let ctorUnique ← TCM.freshUnique ctorQualifiedName
  let info : GlobalInfo := {
    name := ⟨ctorUnique⟩
    type := ctorType
    value := none
    isConstructor := true
    ctorTag := ctorTag
    origin := .constructor
  }
  let mut g := globals.insert ctorQualifiedName info
  g := g.insertInChild typeName.display ctorSimpleName info
  let ctorMeta : ConstructorMeta := {
    name := info.name
    simpleName := ctorSimpleName
    tag := ctorTag
    arity := fieldTypes.size
    type := ctorType
  }
  g := g.registerConstructorMeta typeName.display ctorMeta
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
  let recordNameStr := recordName.display
  let mut g := globals

  if !isDirty then
    if let some prev := prevGlobals then
      for (fieldNameOpt, _) in fields do
        if let some fieldName := fieldNameOpt then
          let accessorNameStr := s!"{recordNameStr}::{fieldName}"
          if let some accessorInfo := prev.lookup accessorNameStr then
            g := g.insert accessorNameStr accessorInfo
            g := g.insertInChild recordNameStr fieldName accessorInfo
      return g

  for (fieldNameOpt, _) in fields do
    if let some fieldName := fieldNameOpt then
      let accessorNameStr := s!"{recordNameStr}::{fieldName}"
      let accessorUnique ← TCM.freshUnique accessorNameStr
      let accessorType ← TCM.freshMetaVal (.vType .zero)
      let accessorInfo : GlobalInfo := {
        name := ⟨accessorUnique⟩
        type := accessorType
        value := none
        isConstructor := false
        origin := .projection
      }
      g := g.insert accessorNameStr accessorInfo
      g := g.insertInChild recordNameStr fieldName accessorInfo
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
    paramKinds := paramKinds.push (param.name.value, kind)

  let mut elabEnv := Elaborate.ElabEnv.empty
  for (paramName, kind) in paramKinds do
    elabEnv := elabEnv.extend paramName kind
  let methodTypeBody ← TCM.withGlobals globals (Elaborate.elaborateType elabEnv methodTypeSyntax)
  let mut methodType := methodTypeBody
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
  let methodNameStr := methodName.display

  -- Check if we can reuse from previous globals
  if !isDirty then
    if let some prev := prevGlobals then
      if let some info := prev.lookup methodNameStr then
        return globals.insert methodNameStr info

  -- Must elaborate fresh
  let methodType ← TCM.recoverWithM
    (elaborateMethodType globals typeClass methodTypeSyntax)
    (TCM.typePlaceholder Span.uninhabited)
  let methodUnique ← TCM.freshUnique methodNameStr
  let methodInfo : GlobalInfo := {
    name := ⟨methodUnique⟩
    type := methodType
    value := none
    isConstructor := false
    origin := .traitMethod
  }
  return globals.insert methodNameStr methodInfo

/-- Register or reuse a function, returns updated globals -/
private def registerFunction
    (globals : Globals)
  (fn : Soma.Core.UntypedFunction)
    (prevGlobals : Option Globals)
    (isDirty : Bool)
    : TCM Globals := do
  let fnNameStr := fn.name.display

  -- Check if we can reuse from previous globals
  if !isDirty then
    if let some prev := prevGlobals then
      if let some info := prev.lookup fnNameStr then
        return globals.insert fnNameStr info

  -- Must elaborate fresh
  let fnType ← TCM.recoverWithM
    (match fn.declaredTypeSyntax with
      | some typeSyntax => TCM.withGlobals globals (elaborateFunctionType typeSyntax)
      | none => TCM.freshMetaVal (.vType .zero))
    (TCM.typePlaceholder fn.span)
  let info : GlobalInfo := {
    name := fn.name
    type := fnType
    value := none
    intrinsic := inferIntrinsicInfo fn
    isConstructor := false
    origin := match inferIntrinsicInfo fn with
      | some (.extern _) => if fn.attrs.intrinsic then .intrinsic else .extern
      | some _ => .intrinsic
      | none => .function
  }
  return globals.insert fnNameStr info

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
    | .algebraic _ typeName typeVarNames _ =>
      let nameStr := typeName.display
      let isDirty := dirtyNames.contains nameStr
      globals ← registerDataType globals nameStr .algebraic typeVarNames #[] (some prevGlobals) isDirty
    | .record _ recordName typeVarNames _ fields =>
      let nameStr := recordName.display
      let isDirty := dirtyNames.contains nameStr
      globals ← registerDataType globals nameStr .record typeVarNames (fields.filterMap (·.1)) (some prevGlobals) isDirty

  -- Second pass: Register constructors
  for typeDef in module.types do
    match typeDef with
    | .algebraic _ typeName typeVarNames constructors =>
      let isDirty := dirtyNames.contains typeName.display
      for ctor in constructors do
        globals ← registerConstructor globals typeName typeVarNames ctor (some prevGlobals) isDirty
    | .record _ recordName typeVarNames ctorName fields =>
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
    let typeVarNames := typeClass.params.map (·.name.value)
    if let some classUnique := globals.lookupUnique classNameStr then
      if !isDirty then
        if let some indInfo := prevGlobals.lookupInductive classNameStr then
          globals := { globals with inductives := globals.inductives.insert indInfo.name indInfo }
        else
          globals := globals.registerInductive classNameStr classUnique .record typeVarNames methodFieldNames
      else
        globals := globals.registerInductive classNameStr classUnique .record typeVarNames methodFieldNames
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
