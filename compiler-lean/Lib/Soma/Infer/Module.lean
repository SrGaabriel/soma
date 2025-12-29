/-
  Module-Level Type Inference

  This module provides functions for running type inference on entire modules,
  bridging the gap between Metal lowering and the inference monad.

  Key functions:
  - `buildTypeEnvFromModule`: Build a TypeEnv from an UntypedModule and seed symbols
  - `buildInstanceEnvFromModule`: Build an InstanceEnv from an UntypedModule
  - `inferModule`: Run type inference on all functions in a module
-/

import Soma.Infer.Monad
import Soma.Infer.Gen
import Soma.Infer.Solver
import Soma.Infer.Resolve
import Soma.Metal
import Soma.Unique

namespace Soma.Infer

open Std
open Soma.Typing
open Soma.Metal (UntypedModule UntypedFunction UntypedTypeDef Module Function TypeDef
                 Constructor UntypedConstructor Name BindingId Scope)
open Soma.Syntax (TypeExpr)
open Soma (UniqueSupply)

/-- Resolve a TypeExpr to a MonoTy with a mapping for type variables.
    Returns `none` if the type cannot be resolved. -/
partial def resolveTypeExprWithVars (ty : TypeExpr) (env : TypeEnv) (tyVars : Std.HashMap String TyVarId) : Option MonoTy :=
  match ty with
  | .var name =>
    -- Look up type variable in the provided mapping
    match tyVars.get? name.value with
    | some tyVarId => some (.var tyVarId)
    | none => none

  | .con name =>
    match StarPrimitive.fromName? name.value with
    | some prim => some (.starPrim prim)
    | none =>
      match env.lookupType name.value with
      | some info => some (.con info.typeId)
      | none => none

  | .arrow from_ to _ =>
    match resolveTypeExprWithVars from_ env tyVars, resolveTypeExprWithVars to env tyVars with
    | some fromTy, some toTy => some (.arrow fromTy toTy)
    | _, _ => none

  | .tuple elements _ =>
    let elemTys := elements.filterMap fun e => resolveTypeExprWithVars e env tyVars
    if elemTys.size == elements.size then
      Gen.mkTupleType elemTys
    else
      none

  | .list elem _ =>
    (resolveTypeExprWithVars elem env tyVars).map Ty.array

  | .app fn arg _ =>
    match resolveTypeExprWithVars arg env tyVars with
    | none => none
    | some argTy =>
      match fn with
      | .con name =>
        match HigherPrimitive.fromName? name.value with
        | some .array => some (Ty.array argTy)
        | some .ref => some (Ty.ref argTy)
        | some .io => some (Ty.io argTy)
        | none =>
          match env.lookupType name.value with
          | some typeInfo =>
            some (Gen.applyTypeArgs (Ty.userCon typeInfo.typeId.kind typeInfo.typeId) #[argTy])
          | none => none
      | .app _ _ _ =>
        -- Nested application - collect all args
        match collectTypeAppWithVars fn #[argTy] env tyVars with
        | some (baseName, allArgs) =>
          match HigherPrimitive.fromName? baseName with
          | some .array => some (Ty.array (allArgs[0]?.getD argTy))
          | some .ref => some (Ty.ref (allArgs[0]?.getD argTy))
          | some .io => some (Ty.io (allArgs[0]?.getD argTy))
          | none =>
            match env.lookupType baseName with
            | some typeInfo =>
              some (Gen.applyTypeArgs (Ty.userCon typeInfo.typeId.kind typeInfo.typeId) allArgs)
            | none => none
        | none => none
      | _ => none

  | .forall_ binders body _ =>
    -- If a binder is already in tyVars (from resolveTypeExprToQualified), use that ID
    -- Otherwise, assign a fresh ID starting from the maximum existing ID + 1
    let maxId := tyVars.fold (init := 0) fun acc _ v => max acc (v.id + 1)
    let (newTyVars, _) := binders.foldl (init := (tyVars, maxId)) fun (acc, nextId) binder =>
      let varName := binder.name.value
      match acc.get? varName with
      | some _ => (acc, nextId)
      | none =>
        let kind : Kind := match binder.kind with
          | some kindName => Kind.fromString kindName.value
          | none => .star
        (acc.insert varName ⟨varName, nextId, kind⟩, nextId + 1)
    resolveTypeExprWithVars body env newTyVars
  | .constrained _ body _ => resolveTypeExprWithVars body env tyVars
  | .parens inner _ => resolveTypeExprWithVars inner env tyVars
  | .kinded ty _ _ => resolveTypeExprWithVars ty env tyVars

  | .record fields tail _ =>
    -- Record type: { x :: Int, y :: Bool } or { x :: Int | r }
    let baseRow : RowTy := match tail with
      | some tailName =>
        match tyVars.get? tailName.value with
        | some tyVarId =>
          -- Use the variable if it was bound with row kind
          if tyVarId.kind == .row then .var tyVarId else .rowEmpty
        | none => .rowEmpty -- Unknown tail variable, treat as closed
      | none => .rowEmpty
    -- Build the row type from fields
    let rowTy? := fields.reverse.foldlM (init := baseRow) fun acc (fieldName, fieldTy) =>
      match resolveTypeExprWithVars fieldTy env tyVars with
      | some fieldMonoTy =>
        let labelTy := Ty.lookupOrLiteralLabel fieldName.value tyVars
        some (Ty.rowExtend labelTy fieldMonoTy acc)
      | none => none
    rowTy?.map Ty.record

  | .variant cases tail _ =>
    -- Variant type: < Ok :: Int | Err :: String > or < Ok :: Int | r >
    let baseRow : RowTy := match tail with
      | some tailName =>
        match tyVars.get? tailName.value with
        | some tyVarId =>
          if tyVarId.kind == .row then .var tyVarId else .rowEmpty
        | none => .rowEmpty
      | none => .rowEmpty
    -- Build the row type from cases
    let rowTy? := cases.reverse.foldlM (init := baseRow) fun acc (caseName, caseTy) =>
      match resolveTypeExprWithVars caseTy env tyVars with
      | some caseMonoTy =>
        let labelTy := Ty.lookupOrLiteralLabel caseName.value tyVars
        some (Ty.rowExtend labelTy caseMonoTy acc)
      | none => none
    rowTy?.map Ty.variant
where
  /-- Collect base type name and arguments from nested applications -/
  collectTypeAppWithVars (ty : TypeExpr) (args : Array MonoTy) (env : TypeEnv) (tyVars : Std.HashMap String TyVarId) : Option (String × Array MonoTy) :=
    match ty with
    | .con name => some (name.value, args)
    | .app fn arg _ =>
      match resolveTypeExprWithVars arg env tyVars with
      | some argTy => collectTypeAppWithVars fn (#[argTy] ++ args) env tyVars
      | none => none
    | .parens inner _ => collectTypeAppWithVars inner args env tyVars
    | _ => none

/-- Resolve a TypeExpr to a MonoTy without using InferM (pure version).
    Returns `none` if the type cannot be resolved (unknown type constructor).
    Used for resolving field types in type definitions during environment building. -/
def resolveTypeExprPure (ty : TypeExpr) (env : TypeEnv) : Option MonoTy :=
  resolveTypeExprWithVars ty env {}

/-- Result of building field types from syntax -/
structure FieldBuildResult where
  /-- Array of field types in order -/
  fieldTypes : Array MonoTy
  /-- Map from field name to (index, type) for named fields -/
  fieldsByName : Std.HashMap String (Nat × MonoTy)

/-- Build field types and fieldsByName map from an array of (optional name, type syntax) pairs -/
def buildFieldTypes
    (fields : Array (Option String × TypeExpr))
    (env : TypeEnv)
    (tyVarMap : Std.HashMap String TyVarId)
    : FieldBuildResult := Id.run do
  let mut fieldTypes : Array MonoTy := #[]
  let mut fieldsByName : Std.HashMap String (Nat × MonoTy) := {}
  let mut idx : Nat := 0
  for (fieldName?, tyExpr) in fields do
    match resolveTypeExprWithVars tyExpr env tyVarMap with
    | some fieldTy =>
      fieldTypes := fieldTypes.push fieldTy
      if let some fieldName := fieldName? then
        fieldsByName := fieldsByName.insert fieldName (idx, fieldTy)
      idx := idx + 1
    | none => pure ()
  { fieldTypes, fieldsByName }

/-- Collect type variable binders from forall expressions, respecting kind annotations -/
partial def collectForallBinders (ty : TypeExpr) : Array (String × Kind) :=
  match ty with
  | .forall_ binders body _ =>
    let binderVars := binders.map fun b =>
      let kind := match b.kind with
        | some kindName => Kind.fromString kindName.value
        | none => Kind.star
      (b.name.value, kind)
    binderVars ++ collectForallBinders body
  | .constrained _ body _ => collectForallBinders body
  | .parens inner _ => collectForallBinders inner
  | _ => #[]

/-- Resolve a TypeExpr to a QualifiedType, collecting free type variables -/
def resolveTypeExprToQualified (ty : TypeExpr) (env : TypeEnv) : Option QualifiedType := do
  -- First collect forall binders with their kinds
  let forallBinders := collectForallBinders ty

  -- Build the type variable map from forall binders
  let mut tyVarMap : Std.HashMap String TyVarId := {}
  let mut tyVarList : Array TyVarId := #[]
  let mut nextId : Nat := 0
  for (name, kind) in forallBinders do
    let tyVarId : TyVarId := ⟨name, nextId, kind⟩
    tyVarMap := tyVarMap.insert name tyVarId
    tyVarList := tyVarList.push tyVarId
    nextId := nextId + 1

  -- Also collect any remaining free variables (those not in forall binders)
  let varNames := ty.collectVarNames
  for name in varNames do
    if !tyVarMap.contains name then
      let tyVarId : TyVarId := ⟨name, nextId, .star⟩
      tyVarMap := tyVarMap.insert name tyVarId
      tyVarList := tyVarList.push tyVarId
      nextId := nextId + 1

  let body ← resolveTypeExprWithVars ty env tyVarMap
  return { vars := tyVarList, constraints := #[], body := body }

/-- Build a TypeEnv from an UntypedModule and external function signatures.

    This populates the type environment with:
    1. External functions from the seed environment
    2. Type definitions from the module
    3. Constructors from the module's type definitions

    Takes a UniqueSupply to generate proper unique IDs for type definitions,
    and returns the updated supply to ensure no ID collisions. -/
def buildTypeEnvFromModule
    (m : UntypedModule)
    (externalFunctions : Array (String × FunctionInfo))
    (supply : UniqueSupply)
    (externalTypes : Array (String × TypeInfo) := #[])
    (externalConstructors : Array (String × ConstructorInfo) := #[])
    : TypeEnv × UniqueSupply := Id.run do
  -- Start with empty environment
  let mut env := TypeEnv.empty
  let mut sup := supply

  -- Add external functions
  for (name, info) in externalFunctions do
    env := env.addFunction name info

  -- Add external types from dependencies
  for (name, info) in externalTypes do
    env := env.addType name info

  -- Add external constructors from dependencies
  for (name, info) in externalConstructors do
    env := env.addConstructor name info

  -- Add type definitions from the module
  for typeDef in m.types do
    let typeName := typeDef.name.display
    let typeVarCount := typeDef.typeVarCount

    -- Create type parameters
    let typeParams : Array TyVarId := Array.range typeVarCount |>.map fun i =>
      ⟨s!"t{i}", i, .star⟩

    -- Generate a proper unique ID for this type
    let (typeUnique, sup') := sup.fresh typeName
    sup := sup'

    let typeId : TypeId := {
      module := m.name
      name := typeName
      unique := typeUnique.id
      kind := Kind.nary typeVarCount
    }

    let typeInfo : TypeInfo := {
      typeId := typeId
      params := typeParams
      constructors := {}  -- Will be filled per-constructor below
    }
    env := env.addType typeName typeInfo

    -- Add constructors with resolved field types
    match typeDef with
    | .algebraic name typeVarNames ctors =>
      let typeParams' : Array TyVarId := typeVarNames.mapIdx fun i n =>
        ⟨n, i, .star⟩
      -- Build type variable mapping for resolving field types
      let tyVarMap : Std.HashMap String TyVarId := typeParams'.foldl (init := {}) fun m tv =>
        m.insert tv.name tv

      for ctor in ctors do
        -- Resolve field types from syntax with type variable support
        let fieldTypes := ctor.fieldTypeSyntax.filterMap fun tyExpr =>
          resolveTypeExprWithVars tyExpr env tyVarMap
        let ctorInfo : ConstructorInfo := {
          typeName := name.display
          typeId := typeId
          typeParams := typeParams'
          fieldTypes := fieldTypes
          tag := ctor.tag
        }
        env := env.addConstructor ctor.name.display ctorInfo

    | .struct name typeVarNames ctorName fields =>
      let typeParams' : Array TyVarId := typeVarNames.mapIdx fun i n =>
        ⟨n, i, .star⟩
      let tyVarMap : Std.HashMap String TyVarId := typeParams'.foldl (init := {}) fun m tv =>
        m.insert tv.name tv

      let fieldResult := buildFieldTypes fields env tyVarMap

      let ctorInfo : ConstructorInfo := {
        typeName := name.display
        typeId := typeId
        typeParams := typeParams'
        fieldTypes := fieldResult.fieldTypes
        tag := 0
      }
      env := env.addConstructor ctorName.display ctorInfo

      -- Update TypeInfo with fieldsByName
      if !fieldResult.fieldsByName.isEmpty then
        let updatedTypeInfo : TypeInfo := {
          typeId := typeId
          params := typeParams
          constructors := {}
          fieldsByName := fieldResult.fieldsByName
        }
        env := env.addType typeName updatedTypeInfo

    | .record name typeVarNames fieldNamesAndTypes =>
      let typeParams' : Array TyVarId := typeVarNames.mapIdx fun i n =>
        ⟨n, i, .star⟩
      let tyVarMap : Std.HashMap String TyVarId := typeParams'.foldl (init := {}) fun m tv =>
        m.insert tv.name tv

      -- Convert (String × TypeExpr) to (Option String × TypeExpr) for buildFieldTypes
      let fieldsWithNames := fieldNamesAndTypes.map fun (n, ty) => (some n, ty)
      let fieldResult := buildFieldTypes fieldsWithNames env tyVarMap

      let ctorInfo : ConstructorInfo := {
        typeName := name.display
        typeId := typeId
        typeParams := typeParams'
        fieldTypes := fieldResult.fieldTypes
        tag := 0
      }
      env := env.addConstructor name.display ctorInfo

      -- Update TypeInfo with fieldsByName
      let updatedTypeInfo : TypeInfo := {
        typeId := typeId
        params := typeParams
        constructors := {}
        fieldsByName := fieldResult.fieldsByName
      }
      env := env.addType typeName updatedTypeInfo

  -- Add trait methods from type classes
  for typeClass in m.typeClasses do
    for (methodName, qualType) in typeClass.methods do
      let fnInfo : FunctionInfo := {
        qualType := qualType
        metalName := methodName
      }
      env := env.addFunction methodName.display fnInfo

  return (env, sup)

/-- Look up a built-in class by name -/
def lookupBuiltinClass (name : String) : Option TyCon :=
  match name with
  | "Eq" => some TypeClassName.eq
  | "Ord" => some TypeClassName.ord
  | "Show" => some TypeClassName.show_
  | "Num" => some TypeClassName.num
  | "Functor" => some TypeClassName.functor
  | "Monad" => some TypeClassName.monad
  | _ => none

/-- Resolve a Syntax.Constraint to a Typing.Constraint.
    Returns none if the class name or any type argument cannot be resolved. -/
def resolveConstraintPure
    (c : Syntax.Constraint)
    (typeEnv : TypeEnv)
    (instEnv : InstanceEnv)
    : Option Typing.Constraint :=
  -- Try to resolve the class name
  let className := lookupBuiltinClass c.className.value
    |>.orElse fun () =>
      instEnv.classes.get? c.className.value |>.map (·.name)
  match className with
  | none => none
  | some tycon =>
    -- Resolve all type arguments
    let resolvedArgs := c.args.filterMap fun tyExpr =>
      resolveTypeExprPure tyExpr typeEnv
    -- Only succeed if all args resolved
    if resolvedArgs.size == c.args.size then
      some { className := tycon, args := resolvedArgs }
    else
      none

/-- Build an InstanceEnv from an UntypedModule, seed instances, and type environment.

    This extracts instances from the module's UntypedInstance declarations
    and adds them to the seed environment. Type arguments are resolved from
    syntax using the provided TypeEnv.

    For built-in classes (Eq, Ord, Show, Num, Functor, Monad), we use known TyCons.
    For user-defined type classes, we look them up in the InstanceEnv.classes. -/
def buildInstanceEnvFromModule
    (m : UntypedModule)
    (seed : InstanceEnv)
    (typeEnv : TypeEnv)
    : InstanceEnv := Id.run do
  let mut env := seed

  for inst in m.instances do
    -- Resolve type arguments from syntax
    let resolvedArgs := inst.typeArgsSyntax.filterMap fun tyExpr =>
      resolveTypeExprPure tyExpr typeEnv

    -- Try to resolve the class name to a TyCon
    let className := lookupBuiltinClass inst.className
      |>.orElse fun () =>
        -- Look for user-defined type class
        env.classes.get? inst.className |>.map (·.name)

    match className with
    | some tycon =>
      -- Extract type variables from resolved args
      let typeVars := resolvedArgs.foldl (init := #[]) fun acc ty =>
        acc ++ ty.freeVarsUnique

      -- Resolve constraints from syntax
      let resolvedConstraints := inst.constraintsSyntax.filterMap fun c =>
        resolveConstraintPure c typeEnv env

      let instDecl : InstanceDecl := {
        className := tycon
        args := resolvedArgs
        typeVars := typeVars
        constraints := resolvedConstraints
        id := env.nextId
        span := inst.span
      }
      env := env.addInstance instDecl
    | none =>
      -- Unknown class - skip (will be caught as error during type checking)
      pure ()

  return env

/-- Extract all captured variable types from a typed expression tree.
    Traverses the expression and collects types from all closure nodes.
    Returns a mapping from BindingId to MonoTy for all captured variables. -/
partial def extractCaptureTypes {scope : Scope} (expr : Metal.TypedExpr scope) : HashMap BindingId MonoTy :=
  go expr {}
where
  go {s : Scope} (e : Metal.TypedExpr s) (acc : HashMap BindingId MonoTy) : HashMap BindingId MonoTy :=
    match e with
    | .closure _liftedName captures _info _span =>
      -- Extract types from this closure's capture list
      captures.toList.foldl (fun m (v, ty) => m.insert v.binding ty) acc
    | .var _ _ _ => acc
    | .lit _ _ => acc
    | .call fn args _ _ => goList args (go fn acc)
    | .let_ _ _ value body _ _ => go body (go value acc)
    | .lam _params body _ _ => go body acc
    | .construct _ _ args _ _ => goList args acc
    | .tuple elems _ _ => goList elems acc
    | .record fields _ _ => goRecordFields fields acc
    | .recordUpdate base updates _ _ => goRecordFields updates (go base acc)
    | .array elems _ _ => goList elems acc
    | .if_ cond then_ else_ _ _ => go else_ (go then_ (go cond acc))
    | .case scrutinees arms _ _ => goArms arms (goList scrutinees acc)
    | .fieldAccess e _ _ _ _ => go e acc
    | .global _ _ _ => acc
    | .panic _ _ _ => acc
    | .proj _ _ _ _ _ => acc
    | .typeApp _ _ _ => acc
    | .inject _ args _ _ => goList args acc
  goList {s : Scope} : Metal.ExprList MonoTy s → HashMap BindingId MonoTy → HashMap BindingId MonoTy
    | .nil, acc => acc
    | .cons e es, acc => goList es (go e acc)
  goArms {s : Scope} : Metal.ArmList MonoTy s → HashMap BindingId MonoTy → HashMap BindingId MonoTy
    | .nil, acc => acc
    | .cons (.mk _pats body _span) as, acc => goArms as (go body acc)
  goRecordFields {s : Scope} : Metal.RecordFieldList MonoTy s → HashMap BindingId MonoTy → HashMap BindingId MonoTy
    | .nil, acc => acc
    | .cons _name expr rest, acc => goRecordFields rest (go expr acc)

/-- Extract binding ID from a typed param triple -/
def typedParamBindingId (p : BindingId × String × MonoTy) : BindingId := p.1

/-- Axiom: when we build paramInfos from fn.params by adding types, the binding IDs are preserved.
    This is true by construction in genFunctionBody. -/
axiom inferFunction_scope_eq (fn : UntypedFunction) (paramInfos : Array (BindingId × String × MonoTy)) :
    fn.params.toList.map Prod.fst = paramInfos.toList.map typedParamBindingId

/-- Result of inferring a single function -/
structure FunctionInferResult where
  /-- The typed function (if successful) -/
  function : Option Function
  /-- Errors encountered -/
  errors : Array InferError

/-- Infer the type of a single untyped function.

    This generates constraints from the function body, solves them,
    and produces a typed function with inferred parameter and return types.

    The key steps are:
    1. Generate constraints - returns typed body with type variable annotations
    2. Solve constraints - produces a substitution
    3. Apply substitution via mapInfo - resolves all type variables to concrete types -/
def inferFunction
    (fn : UntypedFunction)
    (ctx : InferContext)
    : FunctionInferResult := Id.run do
  -- Run inference in the monad
  let (result, finalState) := InferM.run (m := do
    -- Generate constraints and get typed body (with type variable annotations)
    let (bodyTy, typedBody, paramInfos) ← genFunctionBody fn fn.body

    -- Build the full function type for ambiguity checking
    let paramTys := paramInfos.map fun (_, _, ty) => ty
    let fnTyForCheck := paramTys.foldr (init := bodyTy) fun ty acc => Ty.arrow ty acc

    -- Solve constraints (pass function type for ambiguity checking)
    Solver.solve fn.body.span fnTyForCheck

    -- Apply final substitution to get concrete types
    let σ ← InferM.getSubst

    -- Resolve all type variables in parameters
    let finalParamInfos := paramInfos.map fun (b, n, ty) => (b, n, σ.apply ty)

    -- Resolve return type
    let finalReturnTy := σ.apply bodyTy

    -- Apply substitution to the typed body to resolve all type annotations
    let finalBody := typedBody.mapInfo σ.apply

    -- Generalize the function type
    let fnTy := finalParamInfos.foldr (init := finalReturnTy) fun (_, _, ty) acc =>
      Ty.arrow ty acc

    -- Get free type variables for generalization
    let freeVars := fnTy.freeVarsUnique

    -- Get remaining constraints
    let graph ← InferM.getConstraints
    let constraints := graph.classes.map (·.toConstraint)

    -- Filter constraints to those relevant to the free variables
    let relevantConstraints := constraints.filter fun c =>
      c.args.any fun arg => arg.freeVars.any fun v =>
        freeVars.any (·.id == v.id)

    return (finalParamInfos, finalReturnTy, finalBody, freeVars, relevantConstraints)
  ) ctx

  let (paramInfos, returnTy, typedBody, typeVars, constraints) := result
  let errors := finalState.errors

  if errors.isEmpty then
    -- The typed body is at scope fn.params.toList.map Prod.fst
    -- Function.body expects scope paramInfos.toList.map typedParamBindingId
    -- These are equal because paramInfos preserves binding IDs from fn.params
    let castBody : Metal.TypedExpr (paramInfos.toList.map typedParamBindingId) :=
      cast (congrArg Metal.TypedExpr (inferFunction_scope_eq fn paramInfos)) typedBody

    -- Create nominal row lookup from type environment
    let lookupNominalRow : Typing.TypeId → Option Typing.RowTy := fun typeId =>
      match ctx.typeEnv.lookupTypeById typeId with
      | some info =>
        if info.hasFields then some info.toRowTy
        else none
      | none => none

    -- Resolve field indices in the typed body
    let resolvedBody := Resolve.resolveFieldIndices lookupNominalRow castBody

    -- Extract captured variable types from closure nodes in the typed body
    let captureTypeMap := extractCaptureTypes typedBody

    -- Build the typed function
    let typedFunction : Function := {
      name := fn.name
      params := paramInfos
      returnType := returnTy
      body := resolvedBody
      typeVars := typeVars
      constraints := constraints
      closureInfo := fn.closureInfo.map fun ci =>
        let capturedVars := ci.capturedVars.map fun (b, n) =>
          -- Look up captured variable type from the extracted map
          let ty := captureTypeMap.get? b |>.getD (.starPrim .unit)
          (b, n, ty)
        ({ capturedVars } : Metal.ClosureInfo)
      attrs := fn.attrs
    }
    ⟨some typedFunction, #[]⟩
  else
    ⟨none, errors⟩

/-- Result of inferring an entire module -/
structure InferModuleResult where
  /-- The typed module -/
  module : Module
  /-- All inference errors -/
  errors : Array InferError

/-- Run type inference on an entire module.

    This processes all functions in the module, collecting errors
    and producing typed versions where possible. -/
def inferModule
    (m : UntypedModule)
    (ctx : InferContext)
    : InferModuleResult := Id.run do
  let mut typedFunctions : Array Function := #[]
  let mut allErrors : Array InferError := #[]

  -- First pass: add all function signatures to the environment
  -- (for mutual recursion support)
  let mut augmentedCtx := ctx
  for fn in m.functions do
    -- If the function has a declared type signature, resolve it to a QualifiedType
    let qualType : QualifiedType := match fn.declaredTypeSyntax with
      | some tyExpr =>
        match resolveTypeExprToQualified tyExpr ctx.typeEnv with
        | some qt => qt
        | none =>
          -- todo: Report error here instead of silently using Unit
          { vars := #[], constraints := #[], body := .starPrim .unit }
      | none =>
        -- No signature: use placeholder (will be inferred in second pass)
        { vars := #[], constraints := #[], body := .starPrim .unit }
    let fnInfo : FunctionInfo := {
      qualType := qualType
      metalName := fn.name
    }
    augmentedCtx := { augmentedCtx with
      typeEnv := augmentedCtx.typeEnv.addFunction fn.name.display fnInfo
    }

  -- Second pass: infer each function
  for fn in m.functions do
    let fnCtx := { augmentedCtx with currentFunction := some fn.name.display }
    let result := inferFunction fn fnCtx
    allErrors := allErrors ++ result.errors
    match result.function with
    | some typedFn => typedFunctions := typedFunctions.push typedFn
    | none => pure ()

  -- Third pass: type-check instance methods
  let mut typedInstances : Array Metal.Instance := #[]
  for inst in m.instances do
    -- Type-check each method in the instance
    let mut typedMethods : Array Function := #[]
    let mut instanceErrors : Array InferError := #[]

    for method in inst.methods do
      let methodCtx := { augmentedCtx with currentFunction := some method.name.display }
      let result := inferFunction method methodCtx
      instanceErrors := instanceErrors ++ result.errors
      match result.function with
      | some typedMethod => typedMethods := typedMethods.push typedMethod
      | none => pure ()

    allErrors := allErrors ++ instanceErrors

    -- Only add the instance if all methods type-checked successfully
    if typedMethods.size == inst.methods.size then
      -- Resolve instance type from type arguments syntax
      let instanceType := match inst.typeArgsSyntax[0]? with
        | some tyExpr => resolveTypeExprPure tyExpr augmentedCtx.typeEnv |>.getD (.starPrim .unit)
        | none => .starPrim .unit  -- Should not happen for valid instances
      let typedInstance : Metal.Instance := {
        className := inst.className
        instanceType := instanceType
        methods := typedMethods
        span := inst.span
      }
      typedInstances := typedInstances.push typedInstance

  -- Convert untyped type definitions to typed ones
  -- Field types are resolved from syntax using the type environment built earlier
  let typedTypes := m.types.map fun td =>
    match td with
    | .algebraic name typeVarNames ctors =>
      let typeVars : Array TyVarId := typeVarNames.mapIdx fun i n => ⟨n, i, .star⟩
      let tyVarMap : Std.HashMap String TyVarId := typeVars.foldl (init := {}) fun m tv => m.insert tv.name tv
      let typedCtors := ctors.map fun c =>
        -- Resolve field types from syntax
        let fields := c.fieldTypeSyntax.filterMap fun tyExpr =>
          resolveTypeExprWithVars tyExpr augmentedCtx.typeEnv tyVarMap
        ({
          name := c.name
          tag := c.tag
          fields := fields
        } : Constructor)
      TypeDef.algebraic name typeVars typedCtors
    | .struct name typeVarNames ctorName fieldSyntax =>
      let typeVars : Array TyVarId := typeVarNames.mapIdx fun i n => ⟨n, i, .star⟩
      let tyVarMap : Std.HashMap String TyVarId := typeVars.foldl (init := {}) fun m tv => m.insert tv.name tv
      let fields := fieldSyntax.filterMap fun (name?, tyExpr) =>
        (resolveTypeExprWithVars tyExpr augmentedCtx.typeEnv tyVarMap).map (name?, ·)
      TypeDef.struct name typeVars ctorName fields
    | .record name typeVarNames fieldNamesAndTypes =>
      let typeVars : Array TyVarId := typeVarNames.mapIdx fun i n => ⟨n, i, .star⟩
      let tyVarMap : Std.HashMap String TyVarId := typeVars.foldl (init := {}) fun m tv => m.insert tv.name tv
      let fields := fieldNamesAndTypes.filterMap fun (n, tyExpr) =>
        (resolveTypeExprWithVars tyExpr augmentedCtx.typeEnv tyVarMap).map (n, ·)
      TypeDef.record name typeVars fields

  let typedModule : Module := {
    name := m.name
    functions := typedFunctions
    types := typedTypes
    instances := typedInstances
    typeClasses := m.typeClasses
  }

  { module := typedModule, errors := allErrors }

end Soma.Infer
