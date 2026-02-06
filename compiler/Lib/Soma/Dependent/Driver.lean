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
import Soma.Core.Name

namespace Soma.Dependent.Driver

open Soma.Syntax
open Soma.Metal
open Soma.Core (exprToTerm Value Term Level PrimOp FFIOp Intrinsic Name)
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
      #[TCError.positivityViolation typeName reason violationSpan none]

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
      let (bindingId, name) := params[idx]!
      let paramTy := if h : idx < paramTypes.size then paramTypes[idx] else Value.vType .zero
      TCM.withBinding name bindingId paramTy .omega .explicit span do
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
        let bindingId ← TCM.freshBindingId name
        TCM.withBinding name bindingId ty .omega .implicit span do
          bindImplicits (idx + 1) explicitIdx
      else
        -- Explicit parameter
        if h : explicitIdx < explicitParams.size then
          let (bindingId, paramName) := explicitParams[explicitIdx]
          TCM.withBinding paramName bindingId ty .omega .explicit span do
            bindImplicits (idx + 1) (explicitIdx + 1)
        else
          let bindingId ← TCM.freshBindingId name
          TCM.withBinding name bindingId ty .omega .explicit span do
            bindImplicits (idx + 1) (explicitIdx + 1)
  bindImplicits 0 0

/-- Type check a single Metal function using dependent types -/
def checkFunction (fn : Metal.UntypedFunction)
    : TCM (Value × Metal.Expr Value (fn.params.toList.map (·.1))) := do
  let span := fn.body.span
  match fn.declaredTypeSyntax with
  | some typeSyntax =>
    -- Elaborate the declared type signature
    let declaredType ← TCM.recoverWithM
      (Elaborate.elaborateType Elaborate.ElabEnv.empty typeSyntax)
      (TCM.typePlaceholder span)
    -- Extract ALL parameter types (both implicit forall binders and explicit params)
    -- This ensures type variables like label polymorphism variables are in scope
    let (allParams, resultType) ← TCM.recoverWith
      (extractAllParamTypes declaredType fn.params.size)
      (#[], declaredType)
    -- Extend context with ALL bindings and check body against result type
    -- Use infallible to continue even if body checking fails
    -- Now we capture the typed expression instead of discarding it
    let typedBody ← withAllTypeBindings allParams fn.params span do
      TCM.infallible (Soma.Dependent.check fn.body resultType) default
    return (declaredType, typedBody)
  | none =>
    -- No signature: create fresh metavariables for param types
    let paramTypes ← fn.params.mapM fun _ => TCM.freshMetaVal (.vType .zero)
    -- Extend context with parameters and infer body type
    -- Now we capture the typed expression instead of discarding it
    withFunctionParams fn.params paramTypes span do
      let (inferredType, typedBody) ← TCM.infallibleExpr (Soma.Dependent.infer fn.body) span
      return (inferredType, typedBody)

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
def elaborateIndexedCtorType (_typeName : Metal.Name) (_typeVarNames : Array String)
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

/-- Build a Globals enviro      -- Check for builtin higher-kinded types (List, Array, IO, Ref)
nment from all function definitions in a module -/
def buildGlobals (module : Metal.UntypedModule) : TCM Globals := do
  -- Start with existing globals from context to preserve external typeIds
  let ctx ← TCM.getCtx
  let mut globals := ctx.globals

  -- First pass: Register all data types (so they can be referenced by functions and constructors)
  for typeDef in module.types do
    match typeDef with
    | .algebraic typeName _typeVarNames _ =>
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
    | .struct structName _typeVarNames _ _ =>
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
        -- Also register without the prefix for unqualified access, but only if it doesn't conflict with an existing type
        if !globals.defs.contains ctorSimpleName then
          globals := globals.insert ctorSimpleName info
    | .struct structName typeVarNames ctorName fields =>
      -- Elaborate struct constructor type from field types
      let fieldTypes := fields.map (·.2)
      let ctorType ← TCM.recoverWithM
        (TCM.withGlobals globals (elaborateCtorType structName typeVarNames fieldTypes))
        (TCM.typePlaceholder Span.uninhabited) -- todo: review if Span.uninhabited is appropriate here
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
      -- Also register without the prefix for unqualified access, but only if it doesn't conflict
      if !globals.defs.contains ctorSimpleName then
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
        (TCM.typePlaceholder Span.uninhabited) -- todo: review if Span.uninhabited is appropriate here

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
    -- Use elaborateFunctionType to properly handle free type variables as implicit foralls
    let fnType ← TCM.recoverWithM
      (match fn.declaredTypeSyntax with
        | some typeSyntax => TCM.withGlobals globals (elaborateFunctionType typeSyntax)
        | none => TCM.freshMetaVal (.vType .zero))
      (TCM.typePlaceholder fn.body.span)
    let info : GlobalInfo := { name := fn.name, type := fnType, value := none, isConstructor := false }
    globals := globals.insert fn.name.display info

  return globals

/-- Build the InstanceEnv from module type classes and instances -/
def buildInstanceEnv (module : Metal.UntypedModule) (_moduleName : String)
    : TCM (InstanceEnv × TraitElaborate.InstanceMap) := do
  TraitElaborate.buildInstanceEnvFromModule module

/-- Build the InstanceEnv incrementally, reusing cached info for unchanged definitions -/
def buildInstanceEnvIncremental
    (module : Metal.UntypedModule)
    (_moduleName : String)
    (prevEnv : InstanceEnv)
    (prevInstanceMap : TraitElaborate.InstanceMap)
    (dirtyNames : Std.HashSet String)
    : TCM (InstanceEnv × TraitElaborate.InstanceMap) := do
  TraitElaborate.buildInstanceEnvFromModuleIncremental module prevEnv prevInstanceMap dirtyNames

/-- Elaborate a single type abbreviation into an AbbrevInfo.

    For non-parameterized abbreviations like `abbrev CInt = Int32`:
      - Directly elaborates the expansion to a Value

    For parameterized abbreviations like `abbrev MyList a = List a`:
      - Creates an elaboration environment with the type parameters
      - Elaborates the expansion in that environment
      - Wraps the result in Pi types (right to left) -/
def elaborateAbbrev (typeAbbrev : Metal.TypeAbbrev) : TCM AbbrevInfo := do
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
def buildAbbrevEnv (module : Metal.UntypedModule) : TCM AbbrevEnv := do
  let mut env := AbbrevEnv.empty
  for typeAbbrev in module.abbreviations do
    let info ← elaborateAbbrev typeAbbrev
    env := env.insert info
  return env

/-- Register or reuse a data type definition, returns updated globals -/
private def registerDataType
    (globals : Globals)
    (nameStr : String)
    (prevGlobals : Option Globals)
    (isDirty : Bool)
    : TCM Globals := do
  -- Check if we can reuse from previous globals
  if !isDirty then
    if let some prev := prevGlobals then
      if let some info := prev.lookup nameStr then
        let mut g := globals.insert nameStr info
        if let some typeId := prev.lookupTypeId nameStr then
          g := g.registerTypeId nameStr typeId
          TCM.registerTypeId nameStr typeId
        return g

  -- Must elaborate fresh
  let typeUnique ← TCM.freshUnique nameStr
  let typeId : Soma.Core.TypeId := Soma.Core.TypeId.fromUnique typeUnique
  let mut g := globals.registerTypeId nameStr typeId
  TCM.registerTypeId nameStr typeId
  let dataTypeVal := Value.vDataType typeId []
  let dataTypeInfo : GlobalInfo := {
    name := .user typeUnique
    type := Value.vType .zero
    value := some dataTypeVal
    isConstructor := false
  }
  return g.insert nameStr dataTypeInfo

/-- Register or reuse a constructor, returns updated globals -/
private def registerConstructor
    (globals : Globals)
    (typeName : Metal.Name)
    (typeVarNames : Array String)
    (ctor : Metal.UntypedConstructor)
    (prevGlobals : Option Globals)
    (isDirty : Bool)
    : TCM Globals := do
  let ctorSimpleName := ctor.name.ctorSimpleName?.getD ctor.name.display
  let ctorQualifiedName := s!"{typeName.display}.{ctorSimpleName}"

  -- Check if we can reuse from previous globals
  if !isDirty then
    if let some prev := prevGlobals then
      if let some info := prev.lookup ctorQualifiedName then
        let mut g := globals.insert ctorQualifiedName info
        if !g.defs.contains ctorSimpleName then
          g := g.insert ctorSimpleName info
        return g

  -- Must elaborate fresh
  let ctorType ← TCM.recoverWithM
    (match ctor.sigSyntax with
      | some sig => TCM.withGlobals globals (elaborateIndexedCtorType typeName typeVarNames sig)
      | none => TCM.withGlobals globals (elaborateCtorType typeName typeVarNames ctor.fieldTypeSyntax))
    (TCM.typePlaceholder Span.uninhabited)
  let ctorUnique ← TCM.freshUnique ctorQualifiedName
  let info : GlobalInfo := {
    name := .user ctorUnique
    type := ctorType
    value := none
    isConstructor := true
    ctorTag := ctor.tag
  }
  let mut g := globals.insert ctorQualifiedName info
  if !g.defs.contains ctorSimpleName then
    g := g.insert ctorSimpleName info
  return g

/-- Register or reuse a struct constructor and its field accessors, returns updated globals -/
private def registerStructConstructor
    (globals : Globals)
    (structName : Metal.Name)
    (typeVarNames : Array String)
    (ctorName : Metal.Name)
    (fields : Array (Option String × Syntax.TypeExpr))
    (prevGlobals : Option Globals)
    (isDirty : Bool)
    : TCM Globals := do
  let structNameStr := structName.display
  let ctorSimpleName := ctorName.ctorSimpleName?.getD ctorName.display
  let ctorQualifiedName := s!"{structNameStr}.{ctorSimpleName}"

  -- Check if we can reuse from previous globals
  if !isDirty then
    if let some prev := prevGlobals then
      if let some info := prev.lookup ctorQualifiedName then
        let mut g := globals.insert ctorQualifiedName info
        if !g.defs.contains ctorSimpleName then
          g := g.insert ctorSimpleName info
        -- Also restore field accessors
        for (fieldNameOpt, _) in fields do
          if let some fieldName := fieldNameOpt then
            let accessorNameStr := s!"{structNameStr}.{fieldName}"
            if let some accessorInfo := prev.lookup accessorNameStr then
              g := g.insert accessorNameStr accessorInfo
        return g

  -- Must elaborate fresh
  let fieldTypes := fields.map (·.2)
  let ctorType ← TCM.recoverWithM
    (TCM.withGlobals globals (elaborateCtorType structName typeVarNames fieldTypes))
    (TCM.typePlaceholder Span.uninhabited)
  let structCtorUnique ← TCM.freshUnique ctorQualifiedName
  let info : GlobalInfo := {
    name := .user structCtorUnique
    type := ctorType
    value := none
    isConstructor := true
    ctorTag := 0
  }
  let mut g := globals.insert ctorQualifiedName info
  if !g.defs.contains ctorSimpleName then
    g := g.insert ctorSimpleName info

  -- Register field accessors
  for (fieldNameOpt, _) in fields do
    if let some fieldName := fieldNameOpt then
      let accessorNameStr := s!"{structNameStr}.{fieldName}"
      let accessorUnique ← TCM.freshUnique accessorNameStr
      let accessorType ← TCM.freshMetaVal (.vType .zero)
      let accessorInfo : GlobalInfo := {
        name := .user accessorUnique
        type := accessorType
        value := none
        isConstructor := false
      }
      g := g.insert accessorNameStr accessorInfo
  return g

/-- Elaborate a type class method type -/
private def elaborateMethodType
    (globals : Globals)
    (typeClass : Metal.TypeClassMeta)
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
    (typeClass : Metal.TypeClassMeta)
    (methodName : Metal.Name)
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
    name := .user methodUnique
    type := methodType
    value := none
    isConstructor := false
  }
  return globals.insert methodNameStr methodInfo

/-- Register or reuse a function, returns updated globals -/
private def registerFunction
    (globals : Globals)
    (fn : Metal.UntypedFunction)
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
    (TCM.typePlaceholder fn.body.span)
  let info : GlobalInfo := { name := fn.name, type := fnType, value := none, isConstructor := false }
  return globals.insert fnNameStr info

/-- Build a Globals environment incrementally, reusing cached types for unchanged definitions -/
def buildGlobalsIncremental
    (module : Metal.UntypedModule)
    (prevGlobals : Globals)
    (dirtyNames : Std.HashSet String)
    : TCM Globals := do
  let ctx ← TCM.getCtx
  let mut globals := ctx.globals

  -- First pass: Register all data types
  for typeDef in module.types do
    match typeDef with
    | .algebraic typeName _ _ =>
      let nameStr := typeName.display
      let isDirty := dirtyNames.contains nameStr
      globals ← registerDataType globals nameStr (some prevGlobals) isDirty
    | .struct structName _ _ _ =>
      let nameStr := structName.display
      let isDirty := dirtyNames.contains nameStr
      globals ← registerDataType globals nameStr (some prevGlobals) isDirty
    | .record _ _ _ =>
      pure ()

  -- Second pass: Register constructors
  for typeDef in module.types do
    match typeDef with
    | .algebraic typeName typeVarNames constructors =>
      let isDirty := dirtyNames.contains typeName.display
      for ctor in constructors do
        globals ← registerConstructor globals typeName typeVarNames ctor (some prevGlobals) isDirty
    | .struct structName typeVarNames ctorName fields =>
      let isDirty := dirtyNames.contains structName.display
      globals ← registerStructConstructor globals structName typeVarNames ctorName fields (some prevGlobals) isDirty
    | .record _ _ _ =>
      pure ()

  -- Register type class methods
  for typeClass in module.typeClasses do
    let isDirty := dirtyNames.contains typeClass.name.display
    for (methodName, methodTypeSyntax) in typeClass.methodSignatures do
      globals ← registerMethod globals typeClass methodName methodTypeSyntax (some prevGlobals) isDirty

  -- Register all functions
  for fn in module.functions do
    let isDirty := dirtyNames.contains fn.name.display
    globals ← registerFunction globals fn (some prevGlobals) isDirty

  return globals

end Soma.Dependent.Driver
