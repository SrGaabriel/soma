import Soma.Syntax
import Soma.Metal
import Soma.Dependent.Monad
import Soma.Dependent.Infer
import Soma.Dependent.Unify
import Soma.Dependent.Zonk
import Soma.Dependent.Level
import Soma.Dependent.Instance
import Soma.Dependent.Error
import Soma.Dependent.Totality
import Soma.Dependent.Elaborate
import Soma.Dependent.TraitElaborate
import Soma.Unique
import Soma.Core.Eval

namespace Soma.Dependent.Driver

open Soma.Syntax
open Soma.Metal
open Soma.Core (exprToTerm Value Term Level)
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

/-- Check totality for a function if it's marked @[total] -/
def checkFunctionTotality (fn : Metal.UntypedFunction) (body : Term)
    (registry : Totality.TotalityRegistry) : Totality.TotalityRegistry × Array TCError :=
  let fnInfo : Totality.FunctionInfo := {
    name := fn.name
    markedTotal := fn.attrs.total
    status := .isUnknown
    params := fn.params.map (·.2)
    fnType := Value.vType .zero
    span := fn.body.span
  }
  let (registry', result) := Totality.checkAndRegisterTotality fnInfo body registry
  (registry', result.errors)

/-- Check positivity for a data type definition -/
def checkDataTypePositivity (typeDef : Metal.UntypedTypeDef) (ctx : TCContext) (state : TCState)
    : Array TCError :=
  match typeDef with
  | .algebraic name _params constructors =>
    -- Look up the registered TypeId, or create a placeholder
    let typeName := name.display
    let typeId : Soma.Core.TypeId := match ctx.globals.lookupTypeId typeName with
      | some id => id
      | none => ⟨state.uniqueSupply.module, typeName, state.uniqueSupply.nextId⟩

    -- Elaborate each constructor's field types
    let ctorTypes := constructors.foldl (init := #[]) fun acc ctor =>
      ctor.fieldTypeSyntax.foldl (init := acc) fun acc2 fieldTyExpr =>
        match (Elaborate.elaborateType Elaborate.ElabEnv.empty fieldTyExpr).run ctx state with
        | .ok (fieldVal, _) => acc2.push fieldVal
        | .error _ => acc2  -- Skip fields that fail to elaborate

    -- Run positivity check
    match Totality.checkDataTypePositivity typeId ctorTypes Span.uninhabited with
    | .ok => #[]
    | .violated reason violationSpan =>
      #[TCError.positivityViolation typeName reason violationSpan]

  | .struct _ _ _ _ =>
    -- Structs are always positive (they're just records)
    #[]

  | .record _ _ _ =>
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

/-- Extract ALL parameter types from a Pi type (both implicit and explicit) -/
partial def extractAllParamTypes (ty : Value) (numExplicit : Nat)
    : TCM (Array (String × Value × Bool) × Value) := do
  let ty' ← force ty
  match ty' with
  | .vPi _qty binder name dom cod =>
    let isImplicit := binder.isImplicit
    -- If we've consumed all explicit params and this is an explicit param, stop here
    -- and return the whole remaining type as the result
    if numExplicit == 0 && !isImplicit then
      return (#[], ty')
    -- Get the codomain by applying the closure to a dummy value
    let lvl ← TCM.currentLevel
    let dummyArg := Value.vNeutral dom (.nVar ⟨name, lvl⟩)
    let codTy ← applyClosure cod dummyArg
    let remainingExplicit := if isImplicit then numExplicit else numExplicit - 1
    if remainingExplicit == 0 && !isImplicit then
      -- Last explicit parameter, stop here
      return (#[(name, dom, isImplicit)], codTy)
    else
      -- Continue extracting (either implicit param, or more explicit params to go)
      let (restParams, resultTy) ← extractAllParamTypes codTy remainingExplicit
      return (#[(name, dom, isImplicit)] ++ restParams, resultTy)
  | _ =>
    -- Not a Pi type, return remaining as result
    return (#[], ty')

/-- Extend the context with function parameters and run an actions -/
def withFunctionParams (params : Array (Metal.BindingId × String)) (paramTypes : Array Value)
    (span : Span) (action : TCM α) : TCM α := do
  -- Extend context with each parameter
  let rec go (idx : Nat) : TCM α := do
    if idx >= params.size then
      action
    else
      let (_, name) := params[idx]!
      let paramTy := if h : idx < paramTypes.size then paramTypes[idx] else Value.vType .zero
      TCM.withBinding name paramTy .omega .explicit span do
        go (idx + 1)
  go 0

/-- Extend the context with ALL type-level bindings (both implicit forall binders and explicit parameters), then run an action -/
def withAllTypeBindings (allParams : Array (String × Value × Bool))
    (explicitParams : Array (Metal.BindingId × String))
    (span : Span) (action : TCM α) : TCM α := do
  -- First, bind all the implicit type parameters (forall binders)
  let rec bindImplicits (idx : Nat) (explicitIdx : Nat) : TCM α := do
    if idx >= allParams.size then
      action
    else
      let (name, ty, isImplicit) := allParams[idx]!
      if isImplicit then
        -- Implicit type parameter (from forall)
        TCM.withBinding name ty .omega .implicit span do
          bindImplicits (idx + 1) explicitIdx
      else
        -- Explicit parameter, use the name from explicitParams if available
        let paramName := if h : explicitIdx < explicitParams.size
                         then explicitParams[explicitIdx].2
                         else name
        TCM.withBinding paramName ty .omega .explicit span do
          bindImplicits (idx + 1) (explicitIdx + 1)
  bindImplicits 0 0

/-- Type check a single Metal function using dependent types -/
def checkFunction (fn : Metal.UntypedFunction) : TCM Value := do
  let span := fn.body.span
  match fn.declaredTypeSyntax with
  | some typeSyntax =>
    -- Elaborate the declared type signature
    let declaredType ← Elaborate.elaborateType Elaborate.ElabEnv.empty typeSyntax
    -- Extract ALL parameter types (both implicit forall binders and explicit params)
    -- This ensures type variables like label polymorphism variables are in scope
    let (allParams, resultType) ← extractAllParamTypes declaredType fn.params.size
    -- Extend context with ALL bindings and check body against result type
    withAllTypeBindings allParams fn.params span do
      let _ ← Soma.Dependent.check fn.body resultType
    return declaredType
  | none =>
    -- No signature: create fresh metavariables for param types
    let paramTypes ← fn.params.mapM fun _ => TCM.freshMetaVal (.vType .zero)
    -- Extend context with parameters and infer body type
    withFunctionParams fn.params paramTypes span do
      let (inferredType, _) ← Soma.Dependent.infer fn.body
      return inferredType

/-- Elaborate a constructor type: fields -> DataType params -/
def elaborateCtorType (typeName : Metal.Name) (typeVarNames : Array String)
    (fieldTypeSyntax : Array Syntax.TypeExpr) : TCM Value := do
  -- Create an elaboration environment with type variables
  let mut elabEnv := Elaborate.ElabEnv.empty
  let mut typeVarVals : Array Value := #[]

  -- Bind type parameters as implicit forall variables
  for varName in typeVarNames do
    let varVal := Value.vNeutral (.vType .zero) (.nVar ⟨varName, ⟨elabEnv.level⟩⟩)
    typeVarVals := typeVarVals.push varVal
    elabEnv := elabEnv.extend varName (.vType .zero)

  -- Look up the registered TypeId, or create a fresh one if not found
  let typeId ← match ← TCM.lookupTypeId typeName.display with
    | some id => pure id
    | none =>
      let u ← TCM.freshUnique typeName.display
      pure (Soma.Core.TypeId.fromUnique u)

  -- Build the result type: DataType applied to type vars
  let resultType := Value.vDataType typeId typeVarVals.toList

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
def elaborateIndexedCtorType (typeName : Metal.Name) (typeVarNames : Array String)
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

/-- Build a Globals environment from all function definitions in a module -/
def buildGlobals (module : Metal.UntypedModule) : TCM Globals := do
  let mut globals := Globals.empty

  -- First pass: Register all data types (so they can be referenced by functions and constructors)
  for typeDef in module.types do
    match typeDef with
    | .algebraic typeName typeVarNames _ =>
      -- Generate a proper TypeId for this data type
      let typeUnique ← TCM.freshUnique typeName.display
      let typeId : Soma.Core.TypeId := Soma.Core.TypeId.fromUnique typeUnique
      -- Register the TypeId in both local globals and TCM context
      globals := globals.registerTypeId typeName.display typeId
      TCM.registerTypeId typeName.display typeId

      -- Register the data type name itself (for evaluation of Term.global)
      let dataTypeVal := Value.vDataType typeId []
      let dataTypeInfo : GlobalInfo := {
        name := .user typeUnique
        type := Value.vType .zero  -- The type of the data type is Type
        value := some dataTypeVal
        isConstructor := false
      }
      globals := globals.insert typeName.display dataTypeInfo
    | .struct structName typeVarNames _ _ =>
      -- Generate a proper TypeId for this struct
      let typeUnique ← TCM.freshUnique structName.display
      let typeId : Soma.Core.TypeId := Soma.Core.TypeId.fromUnique typeUnique
      -- Register the TypeId in both local globals and TCM context
      globals := globals.registerTypeId structName.display typeId
      TCM.registerTypeId structName.display typeId

      -- Register the struct type name itself
      let dataTypeVal := Value.vDataType typeId []
      let dataTypeInfo : GlobalInfo := {
        name := .user typeUnique
        type := Value.vType .zero
        value := some dataTypeVal
        isConstructor := false
      }
      globals := globals.insert structName.display dataTypeInfo
    | .record _ _ _ =>
      pure ()

  -- Second pass: Register constructors (now data types are available for reference)
  for typeDef in module.types do
    match typeDef with
    | .algebraic typeName typeVarNames constructors =>
      for ctor in constructors do
        -- Elaborate the constructor type by checking wheter indexed (has signature) or simple (has fields)
        -- Use withGlobals so the TCM context sees the registered data types
        let ctorType ← match ctor.sigSyntax with
          | some sig =>
            -- Indexed constructor: elaborate full signature
            TCM.withGlobals globals (elaborateIndexedCtorType typeName typeVarNames sig)
          | none =>
            -- Simple constructor: build type from fields
            TCM.withGlobals globals (elaborateCtorType typeName typeVarNames ctor.fieldTypeSyntax)
        -- Get the simple constructor name
        let ctorSimpleName := ctor.name.ctorSimpleName?.getD ctor.name.display
        let ctorQualifiedName := s!"{typeName.display}.{ctorSimpleName}"
        let ctorUnique ← TCM.freshUnique ctorQualifiedName
        let ctorCoreName : Soma.Core.Name := .user ctorUnique
        let info : GlobalInfo := {
          name := ctorCoreName
          type := ctorType
          value := none
          isConstructor := true
          ctorTag := ctor.tag
        }
        globals := globals.insert ctorQualifiedName info
        -- Also register without the prefix for unqualified access
        globals := globals.insert ctorSimpleName info
    | .struct structName typeVarNames ctorName fields =>
      -- Elaborate struct constructor type from field types
      let fieldTypes := fields.map (·.2)
      let ctorType ← TCM.withGlobals globals (elaborateCtorType structName typeVarNames fieldTypes)
      -- Get the simple constructor name
      let ctorSimpleName := ctorName.ctorSimpleName?.getD ctorName.display
      let ctorQualifiedName := s!"{structName.display}.{ctorSimpleName}"
      let structCtorUnique ← TCM.freshUnique ctorQualifiedName
      let structCtorCoreName : Soma.Core.Name := .user structCtorUnique
      let info : GlobalInfo := {
        name := structCtorCoreName
        type := ctorType
        value := none
        isConstructor := true
        ctorTag := 0
      }
      globals := globals.insert ctorQualifiedName info
      -- Also register without the prefix for unqualified access
      globals := globals.insert ctorSimpleName info
      -- Register field accessors
      for (fieldNameOpt, _) in fields do
        if let some fieldName := fieldNameOpt then
          let accessorNameStr := s!"{structName.display}.{fieldName}"
          let accessorUnique ← TCM.freshUnique accessorNameStr
          let accessorType ← TCM.freshMetaVal (.vType .zero)
          let accessorInfo : GlobalInfo := {
            name := .user accessorUnique
            type := accessorType
            value := none
            isConstructor := false
          }
          globals := globals.insert accessorNameStr accessorInfo
    | .record _ _ _ =>
      pure ()

  -- Register type class methods as globals
  for typeClass in module.typeClasses do
    for (methodName, methodTypeSyntax) in typeClass.methodSignatures do
      -- Build an elaboration environment with the trait's type parameters
      let mut elabEnv := Elaborate.ElabEnv.empty
      for paramName in typeClass.paramNames do
        elabEnv := elabEnv.extend paramName (Value.vType Level.zero)

      -- Elaborate the method type signature with type params in scope
      let methodTypeBody ← TCM.withGlobals globals (Elaborate.elaborateType elabEnv methodTypeSyntax)

      -- Wrap in implicit foralls for type parameters (right to left)
      let mut methodType := methodTypeBody
      let mut outerEnv := elabEnv
      for paramName in typeClass.paramNames.reverse do
        outerEnv := {
          tyVars := outerEnv.tyVars.tail!
          level := outerEnv.level - 1
        }
        let codClosure ← Elaborate.mkDependentClosure paramName methodType outerEnv
        methodType := Value.vPi .omega .implicit paramName (Value.vType Level.zero) codClosure

      let methodUnique ← TCM.freshUnique methodName.display
      let methodInfo : GlobalInfo := {
        name := .user methodUnique
        type := methodType
        value := none
        isConstructor := false
      }
      globals := globals.insert methodName.display methodInfo

  -- Register all functions (after data types so function signatures can reference them)
  for fn in module.functions do
    -- Elaborate the type signature if present, otherwise create a placeholder
    let fnType ← match fn.declaredTypeSyntax with
      | some typeSyntax => TCM.withGlobals globals (Elaborate.elaborateType Elaborate.ElabEnv.empty typeSyntax)
      | none => TCM.freshMetaVal (.vType .zero)
    let fnUnique ← TCM.freshUnique fn.name.display
    let info : GlobalInfo := { name := .user fnUnique, type := fnType, value := none, isConstructor := false }
    globals := globals.insert fn.name.display info

  return globals

/-- Build the InstanceEnv from module type classes and instances -/
def buildInstanceEnv (module : Metal.UntypedModule) (_moduleName : String) : TCM InstanceEnv := do
  TraitElaborate.buildInstanceEnvFromModule module

end Soma.Dependent.Driver
