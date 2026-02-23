import Soma.Core.Value
import Soma.Core.Quantity
import Soma.Core.Level
import Soma.Core.TypeId
import Soma.Core.Eval
import Soma.Dependent.Monad
import Soma.Dependent.Elaborate
import Soma.Dependent.Infer
import Soma.Dependent.Instance
import Soma.Core.Module
import Soma.Syntax.Ast
import Soma.Unique

namespace Soma.Dependent.TraitElaborate

open Soma (Unique)
open Soma.Core
open Soma.Syntax (TypeExpr Span TypeVarBinder)
open Soma.Dependent.Elaborate (ElabEnv elaborateType mkConstClosure mkDependentClosure)

/-- Maps source spans to their elaborated instance info -/
abbrev InstanceMap := Std.HashMap Span InstanceInfo

structure ClassRegistry where
  byName : Std.HashMap String Unique := {}
  deriving Inhabited

namespace ClassRegistry

def empty : ClassRegistry := {}

def register (r : ClassRegistry) (name : String) (id : Unique) : ClassRegistry :=
  { r with byName := r.byName.insert name id }

def lookup (r : ClassRegistry) (name : String) : Option Unique :=
  r.byName.get? name

end ClassRegistry

/-- Recursively substitute type arguments in a Value.

When we see a neutral variable that matches a type parameter name,
we replace it with the corresponding type argument.
-/
private partial def applyTypeValue (fnVal argVal : Value) : TCM Value := do
  match fnVal with
  | .vDataType id params =>
    return .vDataType id (params ++ [argVal])
  | .vPi _ _ _ _ cod =>
    applyClosure cod argVal
  | .vNeutral ty neu =>
    let resultTy ← match ty with
      | .vPi _ _ _ _ cod => applyClosure cod argVal
      | _ => pure ty
    return .vNeutral resultTy (.nApp neu argVal)
  | _ =>
    return fnVal

private partial def neutralHeadAndArgs (neu : Neutral) : Neutral × List Value :=
  match neu with
  | .nApp fn arg =>
    let (head, args) := neutralHeadAndArgs fn
    (head, args ++ [arg])
  | _ => (neu, [])

partial def substituteTypeArgsInValue (v : Value) (paramNames : Array String)
    (typeArgs : Array Value) (depth : Nat) : TCM Value := do
  let v' ← force v
  match v' with
  | .vNeutral _ (.nVar var) =>
    -- Check if this variable is a type parameter
    match paramNames.findIdx? (· == var.name) with
    | some idx =>
      if h : idx < typeArgs.size then
        return typeArgs[idx]
      else
        return v'
    | none => return v'

  | .vNeutral ty neu =>
    let ty' ← substituteTypeArgsInValue ty paramNames typeArgs depth
    let (head, args) := neutralHeadAndArgs neu
    let args' ← args.mapM (fun a => substituteTypeArgsInValue a paramNames typeArgs depth)
    match head with
    | .nVar var =>
      match paramNames.findIdx? (· == var.name) with
      | some idx =>
        if h : idx < typeArgs.size then
          let base := typeArgs[idx]
          args'.foldlM (init := base) (fun acc arg => applyTypeValue acc arg)
        else
          let rebuilt := args'.foldl (fun acc arg => .nApp acc arg) head
          return .vNeutral ty' rebuilt
      | none =>
        let rebuilt := args'.foldl (fun acc arg => .nApp acc arg) head
        return .vNeutral ty' rebuilt
    | _ =>
      let rebuilt := args'.foldl (fun acc arg => .nApp acc arg) head
      return .vNeutral ty' rebuilt

  | .vPi qty binder name dom cod =>
    let dom' ← substituteTypeArgsInValue dom paramNames typeArgs depth
    -- For the codomain, we need to apply the closure to a fresh variable,
    -- substitute in the body, then rebuild the closure
    let dummyArg := Value.vNeutral dom' (.nVar ⟨name, ⟨depth⟩⟩)
    let codVal ← applyClosure cod dummyArg
    let codVal' ← substituteTypeArgsInValue codVal paramNames typeArgs (depth + 1)
    let codClosure ← mkDependentClosure name codVal' ElabEnv.empty
    return .vPi qty binder name dom' codClosure

  | .vSigma qty name fst snd =>
    let fst' ← substituteTypeArgsInValue fst paramNames typeArgs depth
    let dummyArg := Value.vNeutral fst' (.nVar ⟨name, ⟨depth⟩⟩)
    let sndVal ← applyClosure snd dummyArg
    let sndVal' ← substituteTypeArgsInValue sndVal paramNames typeArgs (depth + 1)
    let sndClosure ← mkDependentClosure name sndVal' ElabEnv.empty
    return .vSigma qty name fst' sndClosure

  | .vRecord row =>
    let row' ← substituteTypeArgsInValue row paramNames typeArgs depth
    return .vRecord row'

  | .vRowExtend label ty tail =>
    let ty' ← substituteTypeArgsInValue ty paramNames typeArgs depth
    let tail' ← substituteTypeArgsInValue tail paramNames typeArgs depth
    return .vRowExtend label ty' tail'

  | .vDataType id params =>
    let params' ← params.mapM (substituteTypeArgsInValue · paramNames typeArgs depth)
    return .vDataType id params'

  | _ => return v'

/-- Extract parameter types from a function type.

For a type like (Int -> Int -> Bool), returns ([Int, Int], Bool).
-/
partial def extractParamTypes (ty : Value) (count : Nat) : TCM (Array Value × Value) := do
  if count == 0 then
    return (#[], ty)
  else
    let ty' ← force ty
    match ty' with
    | .vPi _ binder _ dom cod =>
      let dummyArg ← TCM.freshMetaVal dom
      let codTy ← applyClosure cod dummyArg
      if binder.isImplicit then
        extractParamTypes codTy count
      else
        let (restParams, resultTy) ← extractParamTypes codTy (count - 1)
        return (#[dom] ++ restParams, resultTy)
    | _ =>
      return (#[], ty')

/-! ## Trait Elaboration

Elaborate a type class (trait) declaration into a ClassInfo structure.
The record type for the class is built from the method signatures.
-/

/-- Build the record type for a type class.

For a trait like:
  trait Eq a where
    def eq :: a -> a -> Bool

The record type is:
  forall {a : Type}. { eq : a -> a -> Bool }

We build this by:
1. Creating an elaboration environment with type parameters bound
2. Elaborating each method signature in that environment
3. Building a record row from the method types
4. Wrapping in implicit foralls for type parameters
-/
def elaborateClassRecordType (params : Array TypeVarBinder)
  (methods : Array (QualifiedName × TypeExpr)) : TCM Value := do
  -- Elaborate kinds for each parameter
  let mut paramKinds : Array (String × Value) := #[]
  for param in params do
    let kind ← match param.kind with
      | some k => Elaborate.elaborateType Elaborate.ElabEnv.empty k
      | none => pure (Value.vType Level.zero)  -- default to Type
    paramKinds := paramKinds.push (param.name.value, kind)

  -- Build elaboration environment with type parameters and their kinds
  let mut elabEnv := ElabEnv.empty
  for (paramName, kind) in paramKinds do
    elabEnv := elabEnv.extend paramName kind

  -- Elaborate each method signature
  let mut fields : List (String × Value) := []
  for (methodName, methodTypeSyntax) in methods do
    let methodType ← elaborateType elabEnv methodTypeSyntax
    fields := (methodName.display, methodType) :: fields

  -- Build the record row from fields (in reverse to preserve order)
  let mut row := Value.vRowEmpty
  for (name, ty) in fields.reverse do
    row := Value.vRowExtend (Value.vLabelLit name) ty row

  -- The base record type
  let recordTy := Value.vRecord row

  -- Wrap in implicit foralls for each type parameter (right to left)
  let mut result := recordTy
  let mut outerEnv := elabEnv
  for (paramName, paramKind) in paramKinds.reverse do
    -- Pop the current variable from the environment
    outerEnv := {
      tyVars := outerEnv.tyVars.tail!
      level := outerEnv.level - 1
    }
    -- Create dependent closure for the codomain
    let codClosure ← mkDependentClosure paramName result outerEnv
    result := Value.vPi .omega .implicit paramName paramKind codClosure

  return result

/-- Elaborate superclass constraints.

For a trait like:
  trait Ord a with (Eq a) where ...

The superclass constraint (Eq a) means:
- Ord's parameter 0 (a) maps to Eq's parameter 0

Returns an array of (superclass Unique, parameter index mapping).
-/
def elaborateSuperclasses (params : Array TypeVarBinder)
    (constraints : Array Syntax.Constraint)
    (registry : ClassRegistry) : TCM (Array (Unique × Array Nat)) := do
  let paramNames := params.map (·.name.value)
  let mut result : Array (Unique × Array Nat) := #[]

  for constraint in constraints do
    match registry.lookup constraint.className.value with
    | none =>
      -- Superclass not found - this will be caught during instance resolution
      pure ()
    | some superclassId =>
      -- Map constraint args to parameter indices
      let mut indices : Array Nat := #[]
      for arg in constraint.args do
        match arg with
        | .var name =>
          match paramNames.findIdx? (· == name.value) with
          | some idx => indices := indices.push idx
          | none => pure ()
        | _ => pure ()
      result := result.push (superclassId, indices)

  return result

/-- Elaborate a single type class into a ClassInfo. -/
def elaborateClass (typeClass : Soma.Core.TypeClassMeta) (registry : ClassRegistry)
    : TCM (ClassInfo × ClassRegistry) := do
  -- Generate a unique ID for this class
  let classUnique ← TCM.freshUnique typeClass.name.display

  -- Elaborate the record type from method signatures
  let recordType ← elaborateClassRecordType typeClass.params typeClass.methodSignatures

  -- Elaborate superclass constraints
  let superclasses ← elaborateSuperclasses typeClass.params typeClass.superclasses registry

  let classInfo : ClassInfo := {
    classId := classUnique
    numParams := typeClass.params.size
    paramQuantities := typeClass.params.map (fun _ => Quantity.omega)
    recordType := recordType
    superclasses := superclasses
    span := Span.uninhabited
  }

  -- Update registry with this class
  let registry' := registry.register typeClass.name.display classUnique

  return (classInfo, registry')

/-! ## Instance Elaboration

Elaborate an instance declaration into an InstanceInfo structure.
The instance value is a record containing the elaborated method implementations.
-/

/-- Elaborate a constraint into (class Unique, arg Values). -/
def elaborateConstraint (constraint : Syntax.Constraint) (env : ElabEnv)
    (registry : ClassRegistry) : TCM (Option (Unique × Array Value)) := do
  match registry.lookup constraint.className.value with
  | none => return none
  | some classId =>
    let args ← constraint.args.mapM (elaborateType env)
    return some (classId, args)

/-- Substitute instance type arguments into a method signature.

For `instance Display Int where def display | x => ...`:
- The class method signature is `a -> String`
- We substitute `a := Int` to get `Int -> String`
-/
def substituteMethodType (methodTypeSyntax : TypeExpr) (params : Array TypeVarBinder)
    (typeArgs : Array Value) : TCM Value := do
  -- Build an environment with type parameters
  let mut elabEnv := ElabEnv.empty
  for param in params do
    let kind ← match param.kind with
      | some k => elaborateType elabEnv k
      | none => pure (Value.vType Level.zero)
    elabEnv := elabEnv.extend param.name.value kind

  let paramNames := params.map (·.name.value)

  -- Elaborate the method type in this environment
  let methodType ← elaborateType elabEnv methodTypeSyntax

  -- Now substitute the actual type arguments for the type parameters
  let substitutedType ← substituteTypeArgsInValue methodType paramNames typeArgs 0
  return substitutedType

/-- Build a lambda value from parameter names and types wrapping a body value. -/
partial def buildLambdaValue (paramNames : Array String) (paramTypes : Array Value)
    (bodyVal : Value) : TCM Value := do
  -- Wrap in lambdas for each parameter (right to left)
  let mut result := bodyVal
  for i in [:paramNames.size] do
    let idx := paramNames.size - 1 - i
    if h₁ : idx < paramNames.size then
      let name := paramNames[idx]
      let paramTy := if h₂ : idx < paramTypes.size then paramTypes[idx] else Value.vType .zero
      let bodyClosure ← mkConstClosure name result
      result := Value.vLam name bodyClosure

  return result

/-- Elaborate a method implementation.

Type-checks the method body against the expected (substituted) signature
and returns the elaborated value.
-/
def elaborateMethodImpl (methodFn : Soma.Core.UntypedFunction) (expectedType : Value) : TCM Value := do
  let paramNames := methodFn.params

  -- Decompose the expected type to get parameter types
  let (paramTypes, _resultType) ← extractParamTypes expectedType paramNames.size

  -- Extend context with params, then elaborate the method body
  let rec bindParams (idx : Nat) : TCM Value := do
    if idx >= paramNames.size then
      let (_, coreBody) ← Soma.Dependent.inferSyntax methodFn.body
      let bodyVal ← TCM.evalExpr coreBody
      return bodyVal
    else
      let name := paramNames[idx]!
      let paramTy := if h : idx < paramTypes.size then paramTypes[idx] else Value.vType .zero
      let bindingId ← TCM.freshLocalId name
      TCM.withBinding name bindingId paramTy .omega
        (Soma.Core.BinderInfo.explicit) methodFn.span do
        bindParams (idx + 1)

  let bodyVal ← bindParams 0

  -- Build the method value as a lambda
  let methodVal ← buildLambdaValue paramNames paramTypes bodyVal

  return methodVal

/-- Build the instance value (a record of method implementations).

For an instance like:
  instance Display Int where
    def display | x => intToString x

We build:
  { display = \x => intToString x }
-/
def elaborateInstanceValue (typeArgs : Array Value)
  (methods : Array Soma.Core.UntypedFunction)
    (methodSignatures : Array (QualifiedName × TypeExpr))
    (params : Array TypeVarBinder) : TCM Value := do
  let mut fields : List (String × Value) := []

  for method in methods do
    -- Find the corresponding method signature
    let methodSig? := methodSignatures.find? fun (name, _) =>
      name.display == method.name.display

    match methodSig? with
    | none =>
      -- Method not in class - skip
      pure ()
    | some (_, sigSyntax) =>
      -- Substitute type arguments into the method signature
      let expectedType ← substituteMethodType sigSyntax params typeArgs

      -- Elaborate the method implementation
      let methodVal ← elaborateMethodImpl method expectedType
      fields := (method.name.display, methodVal) :: fields

  return Value.vRecordVal fields.reverse

/-- Elaborate a single instance declaration into an InstanceInfo. -/
def elaborateInstance (inst : Soma.Core.InstanceDecl) (registry : ClassRegistry)
  (typeClass : Soma.Core.TypeClassMeta) : TCM (Option InstanceInfo) := do
  -- Look up the class this is an instance of
  match registry.lookup inst.className with
  | none =>
    return none
  | some classId =>
    -- Elaborate the type arguments
    let elabEnv := ElabEnv.empty
    let typeArgs ← inst.typeArgsSyntax.mapM (elaborateType elabEnv)

    -- Elaborate the instance constraints
    let mut constraints : Array (Unique × Array Value) := #[]
    for constraint in inst.constraintsSyntax do
      match ← elaborateConstraint constraint elabEnv registry with
      | some c => constraints := constraints.push c
      | none => pure ()

    -- Build the instance value (record of method implementations)
    let instValue ← elaborateInstanceValue
      typeArgs
      inst.methods
      typeClass.methodSignatures
      typeClass.params

    -- Generate instance ID
    let instName := s!"$inst_{inst.className}_{typeArgs.size}"
    let instUnique ← TCM.freshUnique instName

    let instanceInfo : InstanceInfo := {
      instanceId := instUnique
      classId := classId
      args := typeArgs
      argQuantities := typeArgs.map (fun _ => .omega)
      constraints := constraints
      value := instValue
      span := inst.span
    }

    return some instanceInfo

/-! ## Building the Complete Instance Environment -/

/-- Build a complete InstanceEnv from a module's type classes and instances.

This is the main entry point for trait/instance elaboration.
It processes all type classes first (to build the registry),
then processes all instances using that registry.
-/
def buildInstanceEnvFromModule (module : Soma.Core.UntypedModule) : TCM (InstanceEnv × InstanceMap) := do
  -- Start with the default built-in instances (Eq Int, Num Int, etc.)
  let mut env := defaultInstanceEnv
  env := { env with moduleName := module.name }
  let mut instanceMap : InstanceMap := {}

  -- First pass: elaborate all type classes and build the registry
  let mut registry := ClassRegistry.empty
  for typeClass in module.typeClasses do
    let (classInfo, registry') ← elaborateClass typeClass registry
    env := env.addClass classInfo
    registry := registry'

  -- Second pass: elaborate all instances
  for inst in module.instances do
    -- Find the corresponding type class for method signatures
    let typeClass? := module.typeClasses.find? fun tc =>
      tc.name.display == inst.className

    match typeClass? with
    | none =>
      pure ()
    | some typeClass =>
      match ← elaborateInstance inst registry typeClass with
      | some instInfo =>
        env := env.addInstanceWithId instInfo
        instanceMap := instanceMap.insert inst.span instInfo
      | none => pure ()

  return (env, instanceMap)

/-- Build an InstanceEnv incrementally, reusing cached class/instance info for unchanged definitions -/
def buildInstanceEnvFromModuleIncremental
  (module : Soma.Core.UntypedModule)
    (prevEnv : InstanceEnv)
    (prevInstanceMap : InstanceMap)
    (dirtyNames : Std.HashSet String)
    : TCM (InstanceEnv × InstanceMap) := do
  -- Start with the default built-in instances
  let mut env := defaultInstanceEnv
  env := { env with moduleName := module.name }
  let mut instanceMap : InstanceMap := {}

  -- First pass: elaborate type classes, reusing cached ones when possible
  let mut registry := ClassRegistry.empty
  for typeClass in module.typeClasses do
    let className := typeClass.name.display

    if dirtyNames.contains className then
      -- Dirty: re-elaborate
      let (classInfo, registry') ← elaborateClass typeClass registry
      env := env.addClass classInfo
      registry := registry'
    else
      -- Not dirty: try to reuse from previous env
      match prevEnv.classes.toList.find? (fun (_, info) => info.classId.original == className) with
      | some (classUnique, classInfo) =>
        -- Reuse cached class info
        env := env.addClass classInfo
        registry := registry.register className classUnique
      | none =>
        -- Not in cache, must elaborate
        let (classInfo, registry') ← elaborateClass typeClass registry
        env := env.addClass classInfo
        registry := registry'

  -- Second pass: elaborate instances, reusing cached ones when possible
  for inst in module.instances do
    let instClassName := inst.className

    -- Instance is dirty if its class is dirty or the instance itself changed
    let isDirty := dirtyNames.contains instClassName

    if isDirty then
      -- Dirty: re-elaborate
      let typeClass? := module.typeClasses.find? fun tc =>
        tc.name.display == instClassName

      match typeClass? with
      | none => pure ()
      | some typeClass =>
        match ← elaborateInstance inst registry typeClass with
        | some instInfo =>
          env := env.addInstanceWithId instInfo
          instanceMap := instanceMap.insert inst.span instInfo
        | none => pure ()
    else
      -- Not dirty: look up the specific instance by span from previous map
      match prevInstanceMap.get? inst.span with
      | some prevInst =>
        -- Reuse the exact cached instance
        env := env.addInstanceWithId prevInst
        instanceMap := instanceMap.insert inst.span prevInst
      | none =>
        -- Not in cache (shouldn't happen if spans are stable), need to elaborate
        let typeClass? := module.typeClasses.find? fun tc =>
          tc.name.display == instClassName

        match typeClass? with
        | none => pure ()
        | some typeClass =>
          match ← elaborateInstance inst registry typeClass with
          | some instInfo =>
            env := env.addInstanceWithId instInfo
            instanceMap := instanceMap.insert inst.span instInfo
          | none => pure ()

  return (env, instanceMap)

end Soma.Dependent.TraitElaborate
