import Soma.Core.Value
import Soma.Core.Quantity
import Soma.Core.Level
import Soma.Core.Eval
import Soma.Core.Quote
import Soma.Dependent.Monad
import Soma.Dependent.Elaborate
import Soma.Dependent.Infer
import Soma.Dependent.Instance
import Soma.Dependent.Zonk
import Soma.Core.Module
import Soma.Syntax.Ast

namespace Soma.Dependent.TraitElaborate

open Soma (Unique)
open Soma.Core
open Soma.Syntax (TypeExpr Span TypeVarBinder)
open Soma.Dependent.Elaborate (ElabEnv elaborateType mkConstClosure mkDependentClosure quoteValue)

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

/-- Build an evaluation Env of the given size with neutral variables at each level -/
private def buildSubstEnv (depth : Nat) : Env :=
  if depth == 0 then Env.mk [] 0
  else
    let bindings := (List.range depth).reverse.map fun lvl =>
      let name := s!"_sv{lvl}"
      (name, Value.vNeutral (.vType .zero) (.nVar ⟨name, ⟨lvl⟩⟩))
    Env.mk bindings depth

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
    let closureEnv := buildSubstEnv depth
    let bodyExpr := quoteValue codVal' (depth + 1)
    let codClosure := Closure.term name closureEnv bodyExpr
    return .vPi qty binder name dom' codClosure

  | .vSigma qty name fst snd =>
    let fst' ← substituteTypeArgsInValue fst paramNames typeArgs depth
    let dummyArg := Value.vNeutral fst' (.nVar ⟨name, ⟨depth⟩⟩)
    let sndVal ← applyClosure snd dummyArg
    let sndVal' ← substituteTypeArgsInValue sndVal paramNames typeArgs (depth + 1)
    let closureEnv := buildSubstEnv depth
    let bodyExpr := quoteValue sndVal' (depth + 1)
    let sndClosure := Closure.term name closureEnv bodyExpr
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
    paramKinds := paramKinds.push (param.name.name, kind)

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
  let paramNames := params.map (·.name.name)
  let mut result : Array (Unique × Array Nat) := #[]

  for constraint in constraints do
    match registry.lookup constraint.className.name with
    | none =>
      -- Superclass not found - this will be caught during instance resolution
      pure ()
    | some superclassId =>
      -- Map constraint args to parameter indices
      let mut indices : Array Nat := #[]
      for arg in constraint.args do
        match arg with
        | .var name =>
          match paramNames.findIdx? (· == name.name) with
          | some idx => indices := indices.push idx
          | none => pure ()
        | _ => pure ()
      result := result.push (superclassId, indices)

  return result

/-- Elaborate a single type class into a ClassInfo. -/
def elaborateClass (typeClass : Soma.Core.TypeClassMeta) (registry : ClassRegistry)
    : TCM (ClassInfo × ClassRegistry) := do
  let classUnique := typeClass.name.id

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
  match registry.lookup constraint.className.name with
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
    elabEnv := elabEnv.extend param.name.name kind

  let paramNames := params.map (·.name.name)

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

/-- Result of elaborating a single instance method -/
structure MethodElabResult where
  /-- The method value for the instance record -/
  value : Value
  /-- The Core Expr body (before NbE evaluation) -/
  coreBody : Expr
  /-- The full lambda-wrapped Expr (params abstracted, before evaluation) -/
  lambdaExpr : Expr
  /-- The full function type (after instance type argument substitution) -/
  fnType : Value
  /-- Parameter bindings: (Unique, name) pairs -/
  params : Array (Unique × String)

/-- Extract explicit parameter types from a function type, skipping implicit binders -/
private partial def extractParamTypes (ty : Value) (count : Nat) : TCM (Array Value × Value) := do
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

/-- Elaborate a method implementation.

Type-checks the method body against the expected (substituted) signature
and returns the elaborated value -/
def elaborateMethodImpl (methodFn : Soma.Core.UntypedFunction) (expectedType : Value)
    : TCM MethodElabResult := do
  let paramNames := methodFn.params

  -- Decompose the expected type to get explicit parameter types
  let (paramTypes, _resultType) ← extractParamTypes expectedType paramNames.size

  -- Extend context with params, then elaborate the method body
  let rec bindParams (idx : Nat) (accParams : Array (Unique × String))
      : TCM (Value × Expr × Array (Unique × String)) := do
    if idx >= paramNames.size then
      let (_bodyTy, coreBody) ← Soma.Dependent.inferSyntax methodFn.body
      let bodyVal ← TCM.evalExpr coreBody
      return (bodyVal, coreBody, accParams)
    else
      let name := paramNames[idx]!
      let paramTy := if h : idx < paramTypes.size then paramTypes[idx] else Value.vType .zero
      let bindingId ← TCM.freshLocalId name
      TCM.withBinding name bindingId paramTy .omega
        (Soma.Core.BinderInfo.explicit) methodFn.span do
        let paramUnique : Unique := ⟨bindingId.id, bindingId.module, name⟩
        bindParams (idx + 1) (accParams.push (paramUnique, name))

  let (_bodyVal, coreBody, generatedParams) ← bindParams 0 #[]

  let _ ← Soma.Dependent.solvePendingInstances
  let coreBody' ← zonkExpr coreBody
  let expectedType' ← zonkValue expectedType

  -- Build the method value by abstracting fvars into proper lambda binders
  let mut lambdaExpr := coreBody'
  for i in [:generatedParams.size] do
    let idx := generatedParams.size - 1 - i
    let (paramId, paramName) := generatedParams[idx]!
    lambdaExpr := lambdaExpr.abstractFVar paramId
    let domTy := if idx < paramTypes.size then
      Soma.Core.quoteExpr0 paramTypes[idx]!
    else
      Expr.sort Level.zero
    lambdaExpr := .lam .explicit paramName domTy lambdaExpr
  let methodVal ← TCM.evalExpr lambdaExpr

  return {
    value := methodVal
    coreBody := coreBody'
    lambdaExpr := lambdaExpr
    fnType := expectedType'
    params := generatedParams
  }

/-- Extract field names and types from a record type value -/
private partial def extractRecordFields (v : Value) : TCM (Array (String × Value)) := do
  match ← force v with
  | .vRecord row => extractRowFields row
  | _ => pure #[]
where
  extractRowFields (row : Value) : TCM (Array (String × Value)) := do
    match ← force row with
    | .vRowExtend (.vLabelLit name) ty rest =>
      let restFields ← extractRowFields rest
      return #[(name, ty)] ++ restFields
    | .vRowEmpty => return #[]
    | _ => return #[]

/-- Recursively check whether a Value contains an unsolved metavariable -/
private partial def valueContainsMeta : Value → Bool
  | .vNeutral _ (.nMeta _) => true
  | .vNeutral ty neu => valueContainsMeta ty || neutralContainsMeta neu
  | .vDataType _ params => params.any valueContainsMeta
  | .vPi _ _ _ dom cod => valueContainsMeta dom || match cod with
    | .const _ v => valueContainsMeta v
    | .term _ _ _ => false -- can't inspect closure bodies
  | .vSigma _ _ fst snd => valueContainsMeta fst || match snd with
    | .const _ v => valueContainsMeta v
    | .term _ _ _ => false
  | .vPair a b => valueContainsMeta a || valueContainsMeta b
  | .vRowExtend l ft t => valueContainsMeta l || valueContainsMeta ft || valueContainsMeta t
  | .vRecord row => valueContainsMeta row
  | .vVariant row => valueContainsMeta row
  | .vConstructor _ _ args rty => args.any valueContainsMeta || valueContainsMeta rty
  | .vEq _ ty l r => valueContainsMeta ty || valueContainsMeta l || valueContainsMeta r
  | _ => false
where
  neutralContainsMeta : Neutral → Bool
    | .nMeta _ => true
    | .nApp fn arg => neutralContainsMeta fn || valueContainsMeta arg
    | .nFst n | .nSnd n => neutralContainsMeta n
    | .nFieldAccess n _ => neutralContainsMeta n
    | .nCase scrut _ rty => neutralContainsMeta scrut || valueContainsMeta rty
    | .nConst _ ty => valueContainsMeta ty
    | .nVar _ => false

/-- Build the record type for a constraint dict (class record type applied to args) -/
private partial def buildConstraintDictType (constraintClassId : Unique)
    (constraintArgs : Array Value) : TCM Value := do
  let classInfo? ← TCM.lookupClass constraintClassId
  match classInfo? with
  | some ci =>
    let mut rty := ci.recordType
    for arg in constraintArgs do
      match ← force rty with
      | .vPi _ _ _ _ cod => rty ← applyClosure cod arg
      | _ => pure ()
    pure rty
  | none => pure (Value.vType .zero)

/-- Constraint dict info for Expr-level substitution -/
structure ConstraintDictEntry where
  classId : Unique
  dictUnique : Unique
  dictTyExpr : Expr

/-- Resolve constraint dict metas in method bodies via Expr-level substitution -/
private def buildConstraintDictSubst
    (constraintDicts : Array ConstraintDictEntry)
    (pendingBefore : Nat)
    : TCM (Std.HashMap MetaId Expr) := do
  let pending ← TCM.getPendingInstances
  let mut subst : Std.HashMap MetaId Expr := {}
  for i in [pendingBefore:pending.size] do
    let p := pending[i]!
    if ← TCM.isMetaSolved p.metaId then continue
    -- Match this pending instance against our constraint dicts by class ID
    for entry in constraintDicts do
      if p.classId == entry.classId then
        let fvarExpr := Expr.fvar entry.dictUnique entry.dictTyExpr
        subst := subst.insert p.metaId fvarExpr
        -- Mark meta as solved to prevent error reporting
        let dictTy ← buildConstraintDictType entry.classId p.args
        let placeholderVal := Value.vNeutral dictTy
          (.nConst ⟨entry.dictUnique.id, entry.dictUnique.module, entry.dictUnique.original⟩
                   dictTy)
        TCM.solveMeta p.metaId placeholderVal
        break
  return subst

/-- Result of elaborating all instance methods -/
structure InstanceElabResult where
  /-- The instance record value -/
  value : Value
  /-- Typed functions for codegen -/
  typedFns : Array Soma.Core.TypedFunction
  /-- Method names paired with their lambda-wrapped Exprs (for rebuilding) -/
  methodExprs : Array (String × Expr)

/-- Elaborate an instance value -/
partial def elaborateInstanceValueFromClassInfo (classInfo : ClassInfo)
    (typeArgs : Array Value) (methods : Array Soma.Core.UntypedFunction)
    (constraintDicts : Array ConstraintDictEntry := #[])
    : TCM InstanceElabResult := do
  let mut recordTy := classInfo.recordType
  for arg in typeArgs do
    match ← force recordTy with
    | .vPi _ _ _ _ cod =>
      recordTy ← applyClosure cod arg
    | _ => pure ()

  -- Extract method names and types from the concrete record type
  let methodTypes ← extractRecordFields recordTy

  -- Elaborate each method implementation against its expected type
  let mut fields : List (String × Value) := []
  let mut typedFns : Array Soma.Core.TypedFunction := #[]
  let mut methodExprs : Array (String × Expr) := #[]
  for method in methods do
    let methodName := method.name.display
    match methodTypes.find? (fun (name, _) => name == methodName) with
    | some (_, expectedType) =>
      let pendingBefore := (← TCM.getPendingInstances).size
      let result ← elaborateMethodImpl method expectedType

      -- For constrained instances: substitute constraint dict metas with
      -- fvar Exprs in the method body, so abstractFVar can find them later.
      let (lambdaExpr, coreBody) ←
        if constraintDicts.isEmpty then
          pure (result.lambdaExpr, result.coreBody)
        else
          let subst ← buildConstraintDictSubst constraintDicts pendingBefore
          if subst.isEmpty then
            pure (result.lambdaExpr, result.coreBody)
          else
            pure (applyMvarSubst result.lambdaExpr subst,
                  applyMvarSubst result.coreBody subst)

      fields := (methodName, result.value) :: fields
      methodExprs := methodExprs.push (methodName, lambdaExpr)
      typedFns := typedFns.push {
        name := method.name
        params := result.params
        body := coreBody
        fnType := result.fnType
        closureInfo := method.closureInfo
        attrs := method.attrs
      }
    | none => pure ()

  return {
    value := Value.vRecordVal fields.reverse
    typedFns := typedFns
    methodExprs := methodExprs
  }

/-- Result of eager constraint resolution -/
private inductive EagerResolutionResult where
  | resolved (dicts : Array (Unique × Value))
  | unresolvable

/-- Try to eagerly resolve all constraints -/
private def tryEagerResolution
    (constraints : Array (Unique × Array Value))
    : TCM EagerResolutionResult := do
  let mut resolvedDicts : Array (Unique × Value) := #[]
  for (constraintClassId, constraintArgs) in constraints do
    if constraintArgs.any valueContainsMeta then
      return .unresolvable
    let result ← Soma.Dependent.resolveInstance constraintClassId constraintArgs
    match result with
    | .found value _ =>
      resolvedDicts := resolvedDicts.push (constraintClassId, value)
    | _ =>
      return .unresolvable
  return .resolved resolvedDicts

/-- Elaborate an instance with eagerly-resolved constraints -/
private def elaborateWithEagerDicts
    (constraints : Array (Unique × Array Value))
    (resolvedDicts : Array (Unique × Value))
    (span : Span)
    (elabMethods : TCM InstanceElabResult)
    : TCM InstanceElabResult := do
  let mut resolvedInstEnv ← TCM.getInstanceEnv
  for (constraintClassId, constraintArgs) in constraints do
    let dictVal := resolvedDicts.find? (·.1 == constraintClassId) |>.map (·.2)
      |>.getD (Value.vType .zero)
    let tempInst : InstanceInfo := {
      instanceId := ← TCM.freshUnique s!"$resolved_{constraintClassId.original}"
      classId := constraintClassId
      args := constraintArgs
      constraints := #[]
      value := dictVal
      span := span
    }
    resolvedInstEnv := resolvedInstEnv.addInstanceWithId tempInst
  TCM.withInstanceEnv resolvedInstEnv elabMethods

/-- A constraint with an optional user-chosen dict name from instance binders. -/
private structure NamedConstraint where
  classId : Unique
  args : Array Value
  dictName? : Option String

/-- Full dictionary-passing elaboration for constrained instances -/
private def elaborateDictPassingInstance
    (constraints : Array NamedConstraint)
    (span : Span)
    (elabMethods : Array ConstraintDictEntry → TCM InstanceElabResult)
    : TCM (Value × Array Soma.Core.TypedFunction × Nat) := do
  -- 1. Create constraint dict bindings.
  let mut constraintDictBindings : Array (Unique × String × Value) := #[]
  let mut constraintDictEntries : Array ConstraintDictEntry := #[]
  let mut tempInstEnv ← TCM.getInstanceEnv
  for nc in constraints do
    let constraintClassId := nc.classId
    let constraintArgs := nc.args
    -- Use user-chosen name if available, otherwise generate one
    let dictName := match nc.dictName? with
      | some name => name
      | none => s!"$dict_{constraintClassId.original}"
    let dictUnique ← TCM.freshUnique dictName
    let dictTy ← buildConstraintDictType constraintClassId constraintArgs
    let dictTyExpr := Soma.Core.quoteExpr0 dictTy
    let dictVal := Value.vNeutral dictTy
      (.nConst ⟨dictUnique.id, dictUnique.module, dictName⟩ dictTy)
    constraintDictBindings := constraintDictBindings.push (dictUnique, dictName, dictTy)
    constraintDictEntries := constraintDictEntries.push {
      classId := constraintClassId
      dictUnique := dictUnique
      dictTyExpr := dictTyExpr
    }
    let tempInst : InstanceInfo := {
      instanceId := dictUnique
      classId := constraintClassId
      args := constraintArgs
      constraints := #[]
      value := dictVal
      span := span
    }
    tempInstEnv := tempInstEnv.addInstanceWithId tempInst

  -- 2. Elaborate methods within the modified instance env and bindings.
  let result ← TCM.withInstanceEnv tempInstEnv do
    let rec withConstraintBindings (idx : Nat) : TCM InstanceElabResult := do
      if idx >= constraintDictBindings.size then
        elabMethods constraintDictEntries
      else
        let (dictUnique, dictName, dictTy) := constraintDictBindings[idx]!
        TCM.withBinding dictName dictUnique dictTy .omega .instance_ span do
          withConstraintBindings (idx + 1)
    withConstraintBindings 0

  -- 3. Build the instance value: a lambda wrapping the method record.
  let recordExpr := Expr.record (result.methodExprs.map fun (name, expr) => (name, expr))
  let zonkedRecordExpr ← zonkExpr recordExpr

  let mut wrappedExpr := zonkedRecordExpr
  for i in [:constraintDictBindings.size] do
    let idx := constraintDictBindings.size - 1 - i
    let (dictUnique, dictName, dictTy) := constraintDictBindings[idx]!
    wrappedExpr := wrappedExpr.abstractFVar dictUnique
    let domTyExpr := Soma.Core.quoteExpr0 dictTy
    wrappedExpr := .lam .instance_ dictName domTyExpr wrappedExpr

  let instValue ← TCM.evalExpr wrappedExpr

  -- 4. Build TypedFunctions with dict params.
  let mut dictPassedFns := #[]
  for fn in result.typedFns do
    let mut body := fn.body
    let mut fnType := fn.fnType
    let mut extraParams : Array (Unique × String) := #[]
    for i in [:constraintDictBindings.size] do
      let idx := constraintDictBindings.size - 1 - i
      let (dictUnique, dictName, dictTy) := constraintDictBindings[idx]!
      body := body.abstractFVar dictUnique
      let domTyExpr := Soma.Core.quoteExpr0 dictTy
      body := .lam .instance_ dictName domTyExpr body
      fnType := .vPi .omega .instance_ dictName dictTy
        (.const dictName fnType)
      extraParams := #[(dictUnique, dictName)] ++ extraParams
    dictPassedFns := dictPassedFns.push {
      fn with
      body := body
      fnType := fnType
      params := extraParams ++ fn.params
    }

  return (instValue, dictPassedFns, constraints.size)

/-- Build an InstanceInfo from the common fields. -/
private def mkInstanceInfo (instUnique classId : Unique) (typeArgs : Array Value)
    (constraints : Array (Unique × Array Value)) (value : Value)
    (span : Span) (constraintDictCount : Nat := 0) : InstanceInfo := {
  instanceId := instUnique
  classId := classId
  args := typeArgs
  argQuantities := typeArgs.map (fun _ => .omega)
  constraints := constraints
  value := value
  constraintDictCount := constraintDictCount
  span := span
}

/-- Three-tier constrained instance elaboration strategy:
    1. No constraints → direct elaboration
    2. All constraints eagerly resolvable → inline resolved dicts
    3. Unresolvable constraints → full dictionary-passing -/
private def elaborateConstrainedInstance
    (classId instUnique : Unique) (typeArgs : Array Value)
    (namedConstraints : Array NamedConstraint) (span : Span)
    (elabSimple : TCM InstanceElabResult)
    (elabConstrained : Array ConstraintDictEntry → TCM InstanceElabResult)
    : TCM (InstanceInfo × Array Soma.Core.TypedFunction) := do
  let constraints := namedConstraints.map fun nc => (nc.classId, nc.args)
  if namedConstraints.isEmpty then
    let result ← elabSimple
    return (mkInstanceInfo instUnique classId typeArgs constraints result.value span,
            result.typedFns)
  else
    match ← tryEagerResolution constraints with
    | .resolved resolvedDicts =>
      let result ← elaborateWithEagerDicts constraints resolvedDicts span elabSimple
      return (mkInstanceInfo instUnique classId typeArgs constraints result.value span,
              result.typedFns)
    | .unresolvable =>
      let (instValue, dictPassedFns, dictCount) ←
        elaborateDictPassingInstance namedConstraints span elabConstrained
      return (mkInstanceInfo instUnique classId typeArgs constraints instValue span dictCount,
              dictPassedFns)

/-- Process instance binders into an elaboration environment and constraint list.

Explicit type variable binders `{a : Type}` create fresh metas in the elabEnv.
Instance dict binders `{{d : Display a}}` produce constraint entries for dict-passing,
preserving the user-chosen name for use in method bodies.
-/
private def processInstanceBinders (binders : Array Syntax.InstanceBinder)
    (registry : ClassRegistry) (baseEnv : ElabEnv := ElabEnv.empty)
    : TCM (ElabEnv × Array NamedConstraint) := do
  let mut elabEnv := baseEnv
  let mut constraints : Array NamedConstraint := #[]
  for binder in binders do
    match binder with
    | .typeVar name kind _ =>
      -- {a : Type} — create a fresh meta for this type variable
      let kindVal ← elaborateType elabEnv kind
      let metaVal ← TCM.freshMetaVal kindVal
      elabEnv := elabEnv.addOverride name.name metaVal
    | .dictParam name? constraint _ =>
      -- {{d : Display a}} or {{Display a}} — elaborate the constraint
      match ← elaborateConstraint constraint elabEnv registry with
      | some (cid, cargs) =>
        constraints := constraints.push {
          classId := cid, args := cargs, dictName? := name?.map (·.name)
        }
      | none => pure ()
  return (elabEnv, constraints)

partial def elaborateInstanceFromClassInfo (inst : Soma.Core.InstanceDecl)
    (classInfo : ClassInfo) (registry : ClassRegistry)
    : TCM (Option (InstanceInfo × Array Soma.Core.TypedFunction)) := do
  let (elabEnv, constraints) ← processInstanceBinders inst.binders registry
  let typeArgs ← inst.typeArgsSyntax.mapM (elaborateType elabEnv)

  let instUnique ← TCM.freshUnique s!"$inst_{inst.className}_{typeArgs.size}"

  let (instanceInfo, typedFns) ← elaborateConstrainedInstance
    classInfo.classId instUnique typeArgs constraints inst.span
    (elaborateInstanceValueFromClassInfo classInfo typeArgs inst.methods)
    (elaborateInstanceValueFromClassInfo classInfo typeArgs inst.methods ·)

  return some (instanceInfo, typedFns)

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
    (params : Array TypeVarBinder)
    (constraintDicts : Array ConstraintDictEntry := #[])
    : TCM InstanceElabResult := do
  let mut fields : List (String × Value) := []
  let mut typedFns : Array Soma.Core.TypedFunction := #[]
  let mut methodExprs : Array (String × Expr) := #[]

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

      -- Record pending instance count for constraint dict substitution.
      let pendingBefore := (← TCM.getPendingInstances).size

      -- Elaborate the method implementation
      let result ← elaborateMethodImpl method expectedType

      -- For constrained instances: substitute constraint dict metas with
      -- fvar Exprs in the method body.
      let (lambdaExpr, coreBody) ←
        if constraintDicts.isEmpty then
          pure (result.lambdaExpr, result.coreBody)
        else
          let subst ← buildConstraintDictSubst constraintDicts pendingBefore
          if subst.isEmpty then
            pure (result.lambdaExpr, result.coreBody)
          else
            let le := applyMvarSubst result.lambdaExpr subst
            let cb := applyMvarSubst result.coreBody subst
            pure (le, cb)

      fields := (method.name.display, result.value) :: fields
      methodExprs := methodExprs.push (method.name.display, lambdaExpr)
      typedFns := typedFns.push {
        name := method.name
        params := result.params
        body := coreBody
        fnType := result.fnType
        closureInfo := method.closureInfo
        attrs := method.attrs
      }

  return {
    value := Value.vRecordVal fields.reverse
    typedFns := typedFns
    methodExprs := methodExprs
  }

/-- Elaborate a single instance declaration into an InstanceInfo.
    Processes explicit binders for type variables and dictionary parameters,
    then delegates to the constrained instance elaboration pipeline. -/
def elaborateInstance (inst : Soma.Core.InstanceDecl) (registry : ClassRegistry)
  (typeClass : Soma.Core.TypeClassMeta) : TCM (Option (InstanceInfo × Array Soma.Core.TypedFunction)) := do
  match registry.lookup inst.className with
  | none =>
    return none
  | some classId =>
    let (elabEnv, constraints) ← processInstanceBinders inst.binders registry

    let typeArgs ← inst.typeArgsSyntax.mapM (elaborateType elabEnv)

    let instUnique ← TCM.freshUnique s!"$inst_{inst.className}_{typeArgs.size}"

    let elabSimple := elaborateInstanceValue typeArgs inst.methods
      typeClass.methodSignatures typeClass.params
    let (instanceInfo, typedFns) ← elaborateConstrainedInstance
      classId instUnique typeArgs constraints inst.span
      elabSimple
      (fun entries => elaborateInstanceValue typeArgs inst.methods
        typeClass.methodSignatures typeClass.params entries)

    return some (instanceInfo, typedFns)

/-- Build a method dispatch wrapper for a type class method -/
private def buildMethodWrapper (info : GlobalInfo) (methodNameStr : String)
    (fieldIdx : Nat) : TCM (Option TypedFunction) := do
  let mut wrapperParams : Array (Soma.Unique × String) := #[]
  let mut walkTy := info.type
  let mut wrapperTy := info.type
  let mut dictUnique : Soma.Unique := ⟨0, "", "$dict"⟩
  let mut dictDomTy : Value := .vType .zero
  let mut foundInstance := false
  let mut walking := true
  while walking do
    match walkTy with
    | .vPi _qty binder name dom cod =>
      let paramUnique ← TCM.freshUnique name
      if binder == .instance_ then
        wrapperParams := wrapperParams.push (paramUnique, name)
        dictUnique := paramUnique
        dictDomTy := dom
        foundInstance := true
        walking := false
      else if binder.isImplicit then
        let nextTy := cod.applyPure (.vType .zero)
        walkTy := nextTy
        wrapperTy := nextTy
      else
        wrapperParams := wrapperParams.push (paramUnique, name)
        walkTy := cod.applyPure (.vType .zero)
    | _ => walking := false
  if !foundInstance then return none
  let dictTyExpr := Soma.Core.quoteExpr0 dictDomTy
  let body := Soma.Core.Expr.fieldAccess
    (Soma.Core.Expr.fvar dictUnique dictTyExpr)
    methodNameStr
    fieldIdx
  return some {
    name := info.name
    params := wrapperParams
    body := body
    fnType := wrapperTy
    closureInfo := none
    attrs := {}
  }

/-- Merge a module-local instance env with a seed env (from dependencies).
    Classes and instances from both are combined, deduplicating by instance ID. -/
private def mergeInstanceEnvs (local_ seed : InstanceEnv) : InstanceEnv := {
  classes := local_.classes.fold (init := seed.classes) fun acc uid info => acc.insert uid info
  instances := local_.instances.fold (init := seed.instances) fun acc uid insts =>
    match seed.instances.get? uid with
    | none => acc.insert uid insts
    | some existing =>
      let merged := insts.foldl (init := existing) fun a inst =>
        if a.any (·.instanceId == inst.instanceId) then a else a.push inst
      acc.insert uid merged
  moduleName := local_.moduleName
}

/-- Build a complete InstanceEnv from a module's type classes and instances.

This is the main entry point for trait/instance elaboration.
It processes all type classes first (to build the registry),
then processes all instances using that registry. -/
def buildInstanceEnvFromModule (module : Soma.Core.UntypedModule)
    : TCM (InstanceEnv × InstanceMap × Array Soma.Core.TypedFunction) := do
  let mut env := defaultInstanceEnv
  env := { env with moduleName := module.name }
  let mut instanceMap : InstanceMap := {}
  let mut allTypedFns : Array Soma.Core.TypedFunction := #[]

  let seedEnv ← TCM.getInstanceEnv
  let mut registry := ClassRegistry.empty
  for (classUnique, _) in seedEnv.classes.toList do
    registry := registry.register classUnique.original classUnique

  -- First pass: elaborate all type classes and build the registry
  for typeClass in module.typeClasses do
    let (classInfo, registry') ← elaborateClass typeClass registry
    env := env.addClass classInfo
    registry := registry'

  -- Second pass: elaborate all instances.
  -- We elaborate within a progressively enriched instance env so that
  -- later instances can eagerly resolve constraints satisfied by earlier ones.
  for inst in module.instances do
    let typeClass? := module.typeClasses.find? fun tc =>
      tc.name.display == inst.className

    let currentEnv := mergeInstanceEnvs env seedEnv

    match typeClass? with
    | some typeClass =>
      match ← TCM.withInstanceEnv currentEnv do
        elaborateInstance inst registry typeClass
      with
      | some (instInfo, methodFns) =>
        env := env.addInstanceWithId instInfo
        instanceMap := instanceMap.insert inst.span instInfo
        allTypedFns := allTypedFns ++ methodFns
      | none => pure ()
    | none =>
      match registry.lookup inst.className with
      | some classId =>
        let classInfo? := seedEnv.getClass classId
          |>.orElse (fun _ => defaultInstanceEnv.getClass classId)
        match classInfo? with
        | some classInfo =>
          match ← TCM.withInstanceEnv currentEnv do
            elaborateInstanceFromClassInfo inst classInfo registry
          with
          | some (instInfo, methodFns) =>
            env := env.addInstanceWithId instInfo
            instanceMap := instanceMap.insert inst.span instInfo
            allTypedFns := allTypedFns ++ methodFns
          | none => pure ()
        | none => pure ()
      | none => pure ()

  for typeClass in module.typeClasses do
    let mut idx := 0
    for (methodName, _) in typeClass.methodSignatures do
      match ← TCM.lookupGlobalByQN methodName with
      | some info =>
        if let some wrapper ← buildMethodWrapper info methodName.display idx then
          allTypedFns := allTypedFns.push wrapper
      | none => pure ()
      idx := idx + 1

  return (env, instanceMap, allTypedFns)

/-- Build an InstanceEnv incrementally, reusing cached class/instance info for unchanged definitions -/
def buildInstanceEnvFromModuleIncremental
  (module : Soma.Core.UntypedModule)
    (prevEnv : InstanceEnv)
    (prevInstanceMap : InstanceMap)
    (dirtyNames : Std.HashSet String)
    : TCM (InstanceEnv × InstanceMap × Array Soma.Core.TypedFunction) := do
  -- Start with the default built-in instances
  let mut env := defaultInstanceEnv
  env := { env with moduleName := module.name }
  let mut instanceMap : InstanceMap := {}
  let mut allTypedFns : Array Soma.Core.TypedFunction := #[]

  -- Pre-populate registry from the seed instance env (dependency classes)
  let seedEnv ← TCM.getInstanceEnv
  let mut registry := ClassRegistry.empty
  for (classUnique, _) in seedEnv.classes.toList do
    registry := registry.register classUnique.original classUnique

  -- First pass: elaborate type classes, reusing cached ones when possible
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
      | some typeClass =>
        match ← elaborateInstance inst registry typeClass with
        | some (instInfo, methodFns) =>
          env := env.addInstanceWithId instInfo
          instanceMap := instanceMap.insert inst.span instInfo
          allTypedFns := allTypedFns ++ methodFns
        | none => pure ()
      | none =>
        match registry.lookup instClassName with
        | some classId =>
          let classInfo? := seedEnv.getClass classId
            |>.orElse (fun _ => defaultInstanceEnv.getClass classId)
          match classInfo? with
          | some classInfo =>
            match ← elaborateInstanceFromClassInfo inst classInfo registry with
            | some (instInfo, methodFns) =>
              env := env.addInstanceWithId instInfo
              instanceMap := instanceMap.insert inst.span instInfo
              allTypedFns := allTypedFns ++ methodFns
            | none => pure ()
          | none => pure ()
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
        | some typeClass =>
          match ← elaborateInstance inst registry typeClass with
          | some (instInfo, methodFns) =>
            env := env.addInstanceWithId instInfo
            instanceMap := instanceMap.insert inst.span instInfo
            allTypedFns := allTypedFns ++ methodFns
          | none => pure ()
        | none =>
          match registry.lookup instClassName with
          | some classId =>
            let classInfo? := seedEnv.getClass classId
              |>.orElse (fun _ => defaultInstanceEnv.getClass classId)
            match classInfo? with
            | some classInfo =>
              match ← elaborateInstanceFromClassInfo inst classInfo registry with
              | some (instInfo, methodFns) =>
                env := env.addInstanceWithId instInfo
                instanceMap := instanceMap.insert inst.span instInfo
                allTypedFns := allTypedFns ++ methodFns
              | none => pure ()
            | none => pure ()
          | none => pure ()

  -- Third pass: create wrapper TypedFunctions for class methods
  for typeClass in module.typeClasses do
    let mut idx := 0
    for (methodName, _) in typeClass.methodSignatures do
      match ← TCM.lookupGlobalByQN methodName with
      | some info =>
        if let some wrapper ← buildMethodWrapper info methodName.display idx then
          allTypedFns := allTypedFns.push wrapper
      | none => pure ()
      idx := idx + 1

  return (env, instanceMap, allTypedFns)

end Soma.Dependent.TraitElaborate
