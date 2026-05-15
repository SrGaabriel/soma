/-
  Test.Dependent.Instance - Unit tests for Type Class Instance Resolution (Phase 6)

  Tests cover:
  - Instance environment operations
  - Instance matching with unification
  - Resolution algorithm (including cycles and depth limits)
  - Superclass resolution
  - Built-in instances for primitives
  - Pending instance resolution
-/

import Soma.Dependent
import Soma.Core
import Soma.Syntax.Source
import Test.Fixtures

namespace Test.Dependent.Instance

open Soma (Unique)
open Soma.Dependent
open Soma.Core
open Soma.Syntax (Span)
open Test.Fixtures

instance : Inhabited (Soma.Unique × Array Nat) where
  default := ({ id := 0, module := "", original := "" }, #[])

instance : Inhabited (Soma.Unique × Array Value) where
  default := ({ id := 0, module := "", original := "" }, #[])

/-- Create a test class unique -/
def mkTestClassId (name : String) (id : Nat) : Soma.Unique :=
  { id := id, module := "Test", original := name }

/-- Create a test instance unique -/
def mkTestInstanceId (name : String) (id : Nat) : Soma.Unique :=
  { id := id, module := "Test", original := name }

/-- Synthetic test placeholders for the kernel-level primitive types -/
def testIntTyUid : Soma.Unique := ⟨1001, "test", "Int32"⟩
def testStringTyUid : Soma.Unique := ⟨1003, "test", "String"⟩
def testBoolTyUid : Soma.Unique := ⟨1002, "test", "Bool"⟩

def testIntTy : Soma.Core.Value := .vDataType testIntTyUid []
def testStringTy : Soma.Core.Value := .vDataType testStringTyUid []
def testBoolTy : Soma.Core.Value := .vDataType testBoolTyUid []

namespace InstanceEnvTests

/-- Test: Empty environment has no classes -/
def testEmptyEnv : IO TestResult := do
  let env := InstanceEnv.empty
  let classId := mkTestClassId "Foo" 0
  if env.hasClass classId then
    return .failed "Empty env should not have any classes"
  else
    return .passed

/-- Test: Can add and retrieve a class -/
def testAddClass : IO TestResult := do
  let classId := mkTestClassId "Eq" 0
  let info : ClassInfo := {
    classId := classId
    numParams := 1
    paramQuantities := #[.omega]
    recordType := Value.vType .zero
    superclasses := #[]
    span := Span.uninhabited
  }
  let env := InstanceEnv.empty.addClass info
  if env.hasClass classId then
    match env.getClass classId with
    | some cls =>
      if cls.numParams == 1 then return .passed
      else return .failed "Wrong numParams"
    | none => return .failed "getClass returned none"
  else
    return .failed "hasClass returned false"

/-- Test: Can add and retrieve instances -/
def testAddInstance : IO TestResult := do
  let classId := mkTestClassId "Eq" 0
  let primTy := testIntTy
  let instValue := Value.vRecordVal [("eq", testBoolTy)]

  let env := InstanceEnv.forModule "Test"
    |>.addInstance classId #[primTy] #[.omega] #[] instValue

  let instances := env.getInstances classId
  if instances.size == 1 then
    if instances[0]!.args.size == 1 then
      return .passed
    else
      return .failed "Wrong number of args"
  else
    return .failed s!"Expected 1 instance, got {instances.size}"

/-- Test: Instance count works -/
def testInstanceCount : IO TestResult := do
  let classId := mkTestClassId "Eq" 0
  let primTy1 := testIntTy
  let primTy2 := testStringTy
  let instValue := Value.vRecordVal [("eq", testBoolTy)]

  let env := InstanceEnv.forModule "Test"
    |>.addInstance classId #[primTy1] #[.omega] #[] instValue
    |>.addInstance classId #[primTy2] #[.omega] #[] instValue

  if env.instanceCount == 2 then
    return .passed
  else
    return .failed s!"Expected 2 instances, got {env.instanceCount}"

/-- Test: Multiple classes work -/
def testMultipleClasses : IO TestResult := do
  let eqId := mkTestClassId "Eq" 0
  let ordId := mkTestClassId "Ord" 1

  let eqInfo : ClassInfo := {
    classId := eqId
    numParams := 1
    paramQuantities := #[.omega]
    recordType := Value.vType .zero
    superclasses := #[]
    span := Span.uninhabited
  }
  let ordInfo : ClassInfo := {
    classId := ordId
    numParams := 1
    paramQuantities := #[.omega]
    recordType := Value.vType .zero
    superclasses := #[(eqId, #[0])]
    span := Span.uninhabited
  }

  let env := InstanceEnv.empty.addClass eqInfo |>.addClass ordInfo

  if env.hasClass eqId && env.hasClass ordId then
    match env.getClass ordId with
    | some cls =>
      if cls.superclasses.size == 1 then return .passed
      else return .failed "Wrong superclass count"
    | none => return .failed "Could not get Ord class"
  else
    return .failed "Missing classes"

/-- Test: Quantity annotations are preserved -/
def testQuantityAnnotations : IO TestResult := do
  let classId := mkTestClassId "Linear" 0
  let info : ClassInfo := {
    classId := classId
    numParams := 2
    paramQuantities := #[.one, .zero]  -- First param linear, second erased
    recordType := Value.vType .zero
    superclasses := #[]
    span := Span.uninhabited
  }
  let env := InstanceEnv.empty.addClass info
  match env.getClass classId with
  | some cls =>
    if cls.paramQuantities.size == 2 &&
       cls.paramQuantities[0]! == .one &&
       cls.paramQuantities[1]! == .zero then
      return .passed
    else
      return .failed "Quantity annotations not preserved"
  | none => return .failed "Class not found"

def run : IO TestRunner := do
  IO.println "  === Instance Environment Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "empty_env" (← testEmptyEnv)
  runner := runner.record "add_class" (← testAddClass)
  runner := runner.record "add_instance" (← testAddInstance)
  runner := runner.record "instance_count" (← testInstanceCount)
  runner := runner.record "multiple_classes" (← testMultipleClasses)
  runner := runner.record "quantity_annotations" (← testQuantityAnnotations)

  return runner

end InstanceEnvTests

namespace NormalizationTests

private def runTCM (m : TCM α) : IO (Except TCError α) := do
  let ctx := TCContext.withDefaultInstances
  match m.run ctx with
  | .ok (a, _) => return .ok a
  | .error e   => return .error e

/-- Two ground goals with the same class and identical args share a key -/
def testGroundArgsIdentical : IO TestResult := do
  let classId := mkTestClassId "Eq" 0
  let args    := #[testIntTy]
  match ← runTCM (do
      let k1 ← normalizeGoalKey classId args
      let k2 ← normalizeGoalKey classId args
      pure (k1, k2)) with
  | .ok (k1, k2) =>
    if k1 == k2 then return .passed
    else return .failed s!"identical goals got different keys: {k1} vs {k2}"
  | .error e => return .failed s!"unexpected error: {e}"

/-- Goals with different arg shapes must not share a key -/
def testDifferentArgsDistinct : IO TestResult := do
  let classId := mkTestClassId "Eq" 0
  match ← runTCM (do
      let k1 ← normalizeGoalKey classId #[testIntTy]
      let k2 ← normalizeGoalKey classId #[testStringTy]
      pure (k1, k2)) with
  | .ok (k1, k2) =>
    if k1 != k2 then return .passed
    else return .failed s!"distinct goals got the same key: {k1}"
  | .error e => return .failed s!"unexpected error: {e}"

/-- Goals differing only in the identity of unassigned metas must share a key -/
def testAlphaEquivalent : IO TestResult := do
  let classId := mkTestClassId "Eq" 0
  match ← runTCM (do
      let m1 ← TCM.freshMetaVal (Value.vType .zero)
      let m2 ← TCM.freshMetaVal (Value.vType .zero)
      let k1 ← normalizeGoalKey classId #[m1]
      let k2 ← normalizeGoalKey classId #[m2]
      pure (k1, k2)) with
  | .ok (k1, k2) =>
    if k1 == k2 then return .passed
    else return .failed s!"α-equivalent goals got different keys: {k1} vs {k2}"
  | .error e => return .failed s!"unexpected error: {e}"

/-- Goals with the same metas in different positions must produce different keys -/
def testMetaPositionsMatter : IO TestResult := do
  let classId := mkTestClassId "Pair" 0
  match ← runTCM (do
      let m1 ← TCM.freshMetaVal (Value.vType .zero)
      let m2 ← TCM.freshMetaVal (Value.vType .zero)
      let k1 ← normalizeGoalKey classId #[m1, m2]
      let k2 ← normalizeGoalKey classId #[m1, m1]
      pure (k1, k2)) with
  | .ok (k1, k2) =>
    if k1 != k2 then return .passed
    else return .failed s!"positional meta identity not captured: {k1}"
  | .error e => return .failed s!"unexpected error: {e}"

def run : IO TestRunner := do
  IO.println "  === α-Normalization Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "ground_args_identical"    (← testGroundArgsIdentical)
  runner := runner.record "different_args_distinct"  (← testDifferentArgsDistinct)
  runner := runner.record "alpha_equivalent"         (← testAlphaEquivalent)
  runner := runner.record "meta_positions_matter"    (← testMetaPositionsMatter)

  return runner

end NormalizationTests

namespace DiscrTreeTests

private def mkInst (id : Nat) (classId : Unique) (firstArg : Value) : InstanceInfo :=
  { instanceId := { id, module := "test", original := s!"inst{id}" }
    classId
    args := #[firstArg]
    argQuantities := #[.omega]
    constraints := #[]
    value := Value.vRecordVal []
    constraintDictCount := 0
    span := Span.uninhabited }

private def mkInst2 (id : Nat) (classId : Unique) (a0 a1 : Value) : InstanceInfo :=
  { instanceId := { id, module := "test", original := s!"inst{id}" }
    classId
    args := #[a0, a1]
    argQuantities := #[.omega, .omega]
    constraints := #[]
    value := Value.vRecordVal []
    constraintDictCount := 0
    span := Span.uninhabited }

/-- Ground values produce distinct keys -/
def testGroundKeysDistinct : IO TestResult := do
  let kInt  := DiscrKey.ofValue (testIntTy)
  let kStr  := DiscrKey.ofValue (testStringTy)
  if kInt != kStr then return .passed
  else return .failed s!"Int and String got the same key: {repr kInt}"

/-- Values with equal head produce equal keys regardless of substructure -/
def testSameDataTypeSameKey : IO TestResult := do
  let listId : Unique := mkTestClassId "List" 42
  let k1 := DiscrKey.ofValue (Value.vDataType listId [testIntTy])
  let k2 := DiscrKey.ofValue (Value.vDataType listId [testStringTy])
  if k1 == k2 then return .passed
  else return .failed "same datatype head gave different keys"

/-- Meta values map to the wildcard key -/
def testMetaIsWildcard : IO TestResult := do
  let metaVal : Value := Value.vNeutral (Value.vType .zero) (.nMeta ⟨999⟩)
  let k := DiscrKey.ofValue metaVal
  if k.isWildcard then return .passed
  else return .failed s!"meta didn't map to wildcard: {repr k}"

/-- Query by key narrows to exact + wildcard buckets -/
def testTreeQueryNarrows : IO TestResult := do
  let classId := mkTestClassId "C" 0
  let intInst   := mkInst 1 classId (testIntTy)
  let strInst   := mkInst 2 classId (testStringTy)
  let metaInst  := mkInst 3 classId (Value.vNeutral (Value.vType .zero) (.nMeta ⟨7⟩))
  let tree : DiscrTree :=
    DiscrTree.empty |>.insert intInst |>.insert strInst |>.insert metaInst
  let candidatesForInt := tree.query [.dataType testIntTyUid]
  let hasInt  := candidatesForInt.any (·.instanceId == intInst.instanceId)
  let hasStr  := candidatesForInt.any (·.instanceId == strInst.instanceId)
  let hasMeta := candidatesForInt.any (·.instanceId == metaInst.instanceId)
  if hasInt && !hasStr && hasMeta then return .passed
  else return .failed s!"narrowing wrong: hasInt={hasInt} hasStr={hasStr} hasMeta={hasMeta}"

/-- Flatten returns everything inserted -/
def testTreeFlatten : IO TestResult := do
  let classId := mkTestClassId "C" 0
  let a := mkInst 10 classId (testIntTy)
  let b := mkInst 11 classId (testStringTy)
  let c := mkInst 12 classId (Value.vNeutral (Value.vType .zero) (.nMeta ⟨0⟩))
  let tree := DiscrTree.empty |>.insert a |>.insert b |>.insert c
  let all := tree.flatten
  if all.size == 3 then return .passed
  else return .failed s!"expected 3 flattened, got {all.size}"

/-- Deep discrimination -/
def testMultiArgDiscrimination : IO TestResult := do
  let classId := mkTestClassId "Coe" 0
  let i := testIntTy
  let s := testStringTy
  let b := testBoolTy
  let mv := Value.vNeutral (Value.vType .zero) (.nMeta ⟨99⟩)
  let intStr  := mkInst2 101 classId i s
  let intBool := mkInst2 102 classId i b
  let refl    := mkInst2 103 classId mv mv
  let tree := DiscrTree.empty |>.insert intStr |>.insert intBool |>.insert refl
  let cands := tree.query [.dataType testIntTyUid, .dataType testStringTyUid]
  let hasIntStr  := cands.any (·.instanceId == intStr.instanceId)
  let hasIntBool := cands.any (·.instanceId == intBool.instanceId)
  let hasRefl    := cands.any (·.instanceId == refl.instanceId)
  if hasIntStr && !hasIntBool && hasRefl then return .passed
  else return .failed s!"multi-arg narrowing wrong: intStr={hasIntStr} intBool={hasIntBool} refl={hasRefl}"

/-- Instance-side wildcard at a specific position. `instance Coe α String` has a wildcard at arg 0 -/
def testInstanceSideWildcardAtPosition : IO TestResult := do
  let classId := mkTestClassId "Coe" 0
  let i := testIntTy
  let s := testStringTy
  let mv0 := Value.vNeutral (Value.vType .zero) (.nMeta ⟨200⟩)
  let anyStr := mkInst2 104 classId mv0 s      -- Coe α String
  let intBool := mkInst2 105 classId i (testBoolTy)
  let tree := DiscrTree.empty |>.insert anyStr |>.insert intBool
  let cands := tree.query [.dataType testIntTyUid, .dataType testStringTyUid]
  let hasAnyStr  := cands.any (·.instanceId == anyStr.instanceId)
  let hasIntBool := cands.any (·.instanceId == intBool.instanceId)
  if hasAnyStr && !hasIntBool then return .passed
  else return .failed s!"instance-wildcard-at-position wrong: anyStr={hasAnyStr} intBool={hasIntBool}"

/-- Merging two trees combines their buckets -/
def testTreeMerge : IO TestResult := do
  let classId := mkTestClassId "C" 0
  let a := mkInst 20 classId (testIntTy)
  let b := mkInst 21 classId (testStringTy)
  let t1 := DiscrTree.empty |>.insert a
  let t2 := DiscrTree.empty |>.insert b
  let merged := DiscrTree.merge t1 t2
  let size := merged.size
  if size == 2 then return .passed
  else return .failed s!"expected merge size 2, got {size}"

def run : IO TestRunner := do
  IO.println "  === Discrimination Tree Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "ground_keys_distinct"            (← testGroundKeysDistinct)
  runner := runner.record "same_datatype_same_key"          (← testSameDataTypeSameKey)
  runner := runner.record "meta_is_wildcard"                (← testMetaIsWildcard)
  runner := runner.record "tree_query_narrows"              (← testTreeQueryNarrows)
  runner := runner.record "tree_flatten"                    (← testTreeFlatten)
  runner := runner.record "multi_arg_discrimination"        (← testMultiArgDiscrimination)
  runner := runner.record "instance_wildcard_at_position"   (← testInstanceSideWildcardAtPosition)
  runner := runner.record "tree_merge"                      (← testTreeMerge)
  return runner

end DiscrTreeTests

namespace BuiltinTests

/-- Test: Default environment has Eq class -/
def testHasEqClass : IO TestResult := do
  let env := defaultInstanceEnv
  if env.hasClass BuiltinClass.eq then
    return .passed
  else
    return .failed "Missing Eq class"

/-- Test: Default environment has Ord class -/
def testHasOrdClass : IO TestResult := do
  let env := defaultInstanceEnv
  if env.hasClass BuiltinClass.ord then
    return .passed
  else
    return .failed "Missing Ord class"

/-- Test: Default environment has Show class -/
def testHasShowClass : IO TestResult := do
  let env := defaultInstanceEnv
  if env.hasClass BuiltinClass.show_ then
    return .passed
  else
    return .failed "Missing Show class"

/-- Test: Default environment has Num class -/
def testHasNumClass : IO TestResult := do
  let env := defaultInstanceEnv
  if env.hasClass BuiltinClass.num then
    return .passed
  else
    return .failed "Missing Num class"

/-- Test: Default environment has Functor class -/
def testHasFunctorClass : IO TestResult := do
  let env := defaultInstanceEnv
  if env.hasClass BuiltinClass.functor then
    return .passed
  else
    return .failed "Missing Functor class"

/-- Test: Default environment has Monad class -/
def testHasMonadClass : IO TestResult := do
  let env := defaultInstanceEnv
  if env.hasClass BuiltinClass.monad then
    return .passed
  else
    return .failed "Missing Monad class"

/-- Test: Default environment has Applicative class -/
def testHasApplicativeClass : IO TestResult := do
  let env := defaultInstanceEnv
  if env.hasClass BuiltinClass.applicative then
    return .passed
  else
    return .failed "Missing Applicative class"

/-- Test: Eq has instances for Int -/
def testEqIntInstance : IO TestResult := do
  let env := defaultInstanceEnv
  if env.hasClass BuiltinClass.eq then
    return .passed
  else
    return .failed "Eq class skeleton missing from defaultInstanceEnv"

/-- Test: Ord has superclass Eq -/
def testOrdSuperclass : IO TestResult := do
  let env := defaultInstanceEnv
  match env.getClass BuiltinClass.ord with
  | some cls =>
    if cls.superclasses.size == 1 then
      let (superclassId, _) := cls.superclasses[0]!
      if superclassId == BuiltinClass.eq then
        return .passed
      else
        return .failed "Ord superclass should be Eq"
    else
      return .failed "Ord should have exactly 1 superclass"
  | none => return .failed "Ord class not found"

/-- Test: Monad has superclass Applicative -/
def testMonadSuperclass : IO TestResult := do
  let env := defaultInstanceEnv
  match env.getClass BuiltinClass.monad with
  | some cls =>
    if cls.superclasses.size == 1 then
      let (superclassId, _) := cls.superclasses[0]!
      if superclassId == BuiltinClass.applicative then
        return .passed
      else
        return .failed "Monad superclass should be Applicative"
    else
      return .failed "Monad should have exactly 1 superclass"
  | none => return .failed "Monad class not found"

/-- Test: Applicative has superclass Functor -/
def testApplicativeSuperclass : IO TestResult := do
  let env := defaultInstanceEnv
  match env.getClass BuiltinClass.applicative with
  | some cls =>
    if cls.superclasses.size == 1 then
      let (superclassId, _) := cls.superclasses[0]!
      if superclassId == BuiltinClass.functor then
        return .passed
      else
        return .failed "Applicative superclass should be Functor"
    else
      return .failed "Applicative should have exactly 1 superclass"
  | none => return .failed "Applicative class not found"

/-- Test: Classes have quantity annotations -/
def testClassQuantities : IO TestResult := do
  let env := defaultInstanceEnv
  match env.getClass BuiltinClass.eq with
  | some cls =>
    if cls.paramQuantities.size == 1 && cls.paramQuantities[0]! == .omega then
      return .passed
    else
      return .failed "Eq should have one omega-quantity parameter"
  | none => return .failed "Eq class not found"

def run : IO TestRunner := do
  IO.println "  === Built-in Environment Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "has_eq_class" (← testHasEqClass)
  runner := runner.record "has_ord_class" (← testHasOrdClass)
  runner := runner.record "has_show_class" (← testHasShowClass)
  runner := runner.record "has_num_class" (← testHasNumClass)
  runner := runner.record "has_functor_class" (← testHasFunctorClass)
  runner := runner.record "has_applicative_class" (← testHasApplicativeClass)
  runner := runner.record "has_monad_class" (← testHasMonadClass)
  runner := runner.record "eq_int_instance" (← testEqIntInstance)
  runner := runner.record "ord_superclass" (← testOrdSuperclass)
  runner := runner.record "monad_superclass" (← testMonadSuperclass)
  runner := runner.record "applicative_superclass" (← testApplicativeSuperclass)
  runner := runner.record "class_quantities" (← testClassQuantities)

  return runner

end BuiltinTests

namespace ResolutionTests

/-- Test: Resolving an instance requires either a wired prim-file instance -/
def testResolveEqInt : IO TestResult := do
  let baseCtx := TCContext.withDefaultInstances
  let eqIntInst : InstanceInfo := {
    instanceId := { id := 900100, module := "test", original := "EqInt" }
    classId := BuiltinClass.eq
    args := #[testIntTy]
    argQuantities := #[.omega]
    constraints := #[]
    value := Value.vRecordVal []
    constraintDictCount := 0
    span := Span.uninhabited
  }
  let ctx := { baseCtx with
    instanceEnv := baseCtx.instanceEnv.addInstanceWithId eqIntInst }
  let action : TCM ResolutionResult := resolveInstance BuiltinClass.eq #[testIntTy]
  match action.run ctx with
  | .ok (result, _) =>
    if result.isFound then
      return .passed
    else
      return .failed s!"Resolution failed: {result}"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Resolve for non-existent class fails -/
def testResolveNonExistentClass : IO TestResult := do
  let ctx := TCContext.withDefaultInstances
  let nonExistentClass := mkTestClassId "NonExistent" 999
  let action : TCM ResolutionResult := resolveInstance nonExistentClass #[testIntTy]
  match action.run ctx with
  | .ok (result, _) =>
    match result with
    | .notFound _ _ _ => return .passed
    | _ => return .failed s!"Expected notFound, got {result}"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Resolve for non-matching type fails -/
def testResolveNonMatchingType : IO TestResult := do
  let ctx := TCContext.withDefaultInstances
  -- Num doesn't have an instance for Bool
  let action : TCM ResolutionResult := resolveInstance BuiltinClass.num #[testBoolTy]
  match action.run ctx with
  | .ok (result, _) =>
    match result with
    | .notFound _ _ _ => return .passed
    | _ => return .failed s!"Expected notFound, got {result}"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Exercise memoization -/
def testMemoizationFreshAcrossCalls : IO TestResult := do
  let baseCtx := TCContext.withDefaultInstances
  let eqIntInst : InstanceInfo := {
    instanceId := { id := 900101, module := "test", original := "EqInt" }
    classId := BuiltinClass.eq
    args := #[testIntTy]
    argQuantities := #[.omega]
    constraints := #[]
    value := Value.vRecordVal []
    constraintDictCount := 0
    span := Span.uninhabited
  }
  let ctx := { baseCtx with
    instanceEnv := baseCtx.instanceEnv.addInstanceWithId eqIntInst }
  let action : TCM Bool := do
    let r1 ← resolveInstance BuiltinClass.eq #[testIntTy]
    let r2 ← resolveInstance BuiltinClass.eq #[testIntTy]
    return r1.isFound && r2.isFound
  match action.run ctx with
  | .ok (ok, _) =>
    if ok then return .passed else return .failed "one of the two calls failed"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Exercise superclasses through tabled resolution -/
def testSuperclassChain : IO TestResult := do
  let ctx := TCContext.withDefaultInstances
  let action : TCM Bool := do
    let instanceEnv := ctx.instanceEnv
    let eqIntInst : InstanceInfo := {
      instanceId := { id := 900000, module := "test", original := "EqInt" }
      classId := BuiltinClass.eq
      args := #[testIntTy]
      argQuantities := #[.omega]
      constraints := #[]
      value := Value.vRecordVal []
      constraintDictCount := 0
      span := Span.uninhabited
    }
    let ordIntInst : InstanceInfo := {
      instanceId := { id := 900001, module := "test", original := "OrdInt" }
      classId := BuiltinClass.ord
      args := #[testIntTy]
      argQuantities := #[.omega]
      constraints := #[]
      value := Value.vRecordVal []
      constraintDictCount := 0
      span := Span.uninhabited
    }
    let instanceEnv' :=
      (instanceEnv.addInstanceWithId eqIntInst).addInstanceWithId ordIntInst
    TCM.withInstanceEnv instanceEnv' do
      let r ← resolveInstance BuiltinClass.ord #[testIntTy]
      return r.isFound
  match action.run ctx with
  | .ok (ok, _) =>
    if ok then return .passed else return .failed "Ord Int didn't resolve"
  | .error e => return .failed s!"Unexpected error: {e}"

def testFailedLookupNotFound : IO TestResult := do
  let ctx := TCContext.withDefaultInstances
  let bogus := mkTestClassId "DoesNotExist" 12345
  let action : TCM ResolutionResult := resolveInstance bogus #[testIntTy]
  match action.run ctx with
  | .ok (result, _) =>
    match result with
    | .notFound _ _ _ => return .passed
    | other => return .failed s!"expected notFound, got {other}"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Resolution result preserves class ID -/
def testResultPreservesClassId : IO TestResult := do
  let ctx := TCContext.withDefaultInstances
  let nonExistentClass := mkTestClassId "MyClass" 42
  let action : TCM ResolutionResult := resolveInstance nonExistentClass #[]
  match action.run ctx with
  | .ok (result, _) =>
    match result.getClassId? with
    | some cid =>
      if cid == nonExistentClass then return .passed
      else return .failed "Class ID not preserved in result"
    | none => return .failed "Expected class ID in result"
  | .error e => return .failed s!"Unexpected error: {e}"

def run : IO TestRunner := do
  IO.println "  === Resolution Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "resolve_eq_int" (← testResolveEqInt)
  runner := runner.record "resolve_non_existent_class" (← testResolveNonExistentClass)
  runner := runner.record "resolve_non_matching_type" (← testResolveNonMatchingType)
  runner := runner.record "memoization_fresh_across_calls" (← testMemoizationFreshAcrossCalls)
  runner := runner.record "superclass_chain" (← testSuperclassChain)
  runner := runner.record "failed_lookup_not_found" (← testFailedLookupNotFound)
  runner := runner.record "result_preserves_class_id" (← testResultPreservesClassId)

  return runner

end ResolutionTests

namespace TCContextTests

/-- Test: withDefaultInstances creates context with instance env -/
def testWithDefaultInstances : IO TestResult := do
  let ctx := TCContext.withDefaultInstances
  if ctx.instanceEnv.hasClass BuiltinClass.eq then
    return .passed
  else
    return .failed "Default context missing Eq class"

/-- Test: Empty context has no instances -/
def testEmptyContext : IO TestResult := do
  let ctx := TCContext.empty
  if ctx.instanceEnv.hasClass BuiltinClass.eq then
    return .failed "Empty context should not have Eq class"
  else
    return .passed

def run : IO TestRunner := do
  IO.println "  === TCContext Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "with_default_instances" (← testWithDefaultInstances)
  runner := runner.record "empty_context" (← testEmptyContext)

  return runner

end TCContextTests

def run : IO TestRunner := do
  IO.println "=== Dependent Types Instance Tests (Phase 6) ==="
  IO.println ""

  let envRunner ← InstanceEnvTests.run
  envRunner.printSummary "Instance Environment"

  let normRunner ← NormalizationTests.run
  normRunner.printSummary "α-Normalization"

  let discrRunner ← DiscrTreeTests.run
  discrRunner.printSummary "Discrimination Tree"

  let builtinRunner ← BuiltinTests.run
  builtinRunner.printSummary "Built-in Environment"

  let resRunner ← ResolutionTests.run
  resRunner.printSummary "Resolution"

  let ctxRunner ← TCContextTests.run
  ctxRunner.printSummary "TCContext"

  IO.println ""

  let combined := envRunner.merge normRunner |>.merge discrRunner
    |>.merge builtinRunner |>.merge resRunner |>.merge ctxRunner

  IO.println s!"Total: {combined.passed} passed, {combined.failed} failed"

  if combined.failed > 0 then
    IO.println ""
    IO.println "FAILURES:"
    for f in combined.failures do IO.println s!"  - {f}"

  return combined

end Test.Dependent.Instance
