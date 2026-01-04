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
import Soma.Unique
import Soma.Syntax.Source
import Test.Fixtures

namespace Test.Dependent.Instance

open Soma (Unique)
open Soma.Dependent
open Soma.Core
open Soma.Syntax (Span)
open Test.Fixtures

/-! ## Inhabited instances for test types -/

instance : Inhabited (Unique × Array Nat) where
  default := ({ id := 0, module := "", original := "" }, #[])

instance : Inhabited (Unique × Array Value) where
  default := ({ id := 0, module := "", original := "" }, #[])

/-! ## Test Helpers -/

/-- Create a test class unique -/
def mkTestClassId (name : String) (id : Nat) : Unique :=
  { id := id, module := "Test", original := name }

/-- Create a test instance unique -/
def mkTestInstanceId (name : String) (id : Nat) : Unique :=
  { id := id, module := "Test", original := name }

/-! ## Instance Environment Tests -/

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
  let primTy := Value.vPrimTy .int
  let instValue := Value.vRecordVal [("eq", Value.vPrimTy .bool)]

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
  let primTy1 := Value.vPrimTy .int
  let primTy2 := Value.vPrimTy .string
  let instValue := Value.vRecordVal [("eq", Value.vPrimTy .bool)]

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

/-! ## Resolution State Tests -/

namespace ResolutionStateTests

/-- Test: Empty state is not too deep -/
def testEmptyNotTooDeep : IO TestResult := do
  let state := ResolutionState.empty
  if state.tooDeep then
    return .failed "Empty state should not be too deep"
  else
    return .passed

/-- Test: State becomes too deep at max depth -/
def testMaxDepth : IO TestResult := do
  let mut state := ResolutionState.empty
  for _ in [:100] do
    state := state.deeper
  if state.tooDeep then
    return .passed
  else
    return .failed "Should be too deep at depth 100"

/-- Test: Push and pop goals -/
def testPushPopGoals : IO TestResult := do
  let classId := mkTestClassId "Eq" 0
  let state := ResolutionState.empty
    |>.pushGoal classId #[]
    |>.pushGoal classId #[Value.vPrimTy .int]

  if state.activeGoals.size == 2 then
    let state' := state.popGoal
    if state'.activeGoals.size == 1 then
      return .passed
    else
      return .failed "Pop didn't work"
  else
    return .failed s!"Expected 2 goals, got {state.activeGoals.size}"

/-- Test: Cycle detection with same primitive type -/
def testCycleDetectionPrimitive : IO TestResult := do
  let classId := mkTestClassId "Eq" 0
  let args := #[Value.vPrimTy .int]
  let state := ResolutionState.empty.pushGoal classId args
  if state.isActive classId args then
    return .passed
  else
    return .failed "Should detect cycle with same primitive type"

/-- Test: No false positive cycle detection -/
def testNoCycleForDifferentArgs : IO TestResult := do
  let classId := mkTestClassId "Eq" 0
  let state := ResolutionState.empty.pushGoal classId #[Value.vPrimTy .int]
  if state.isActive classId #[Value.vPrimTy .string] then
    return .failed "Should not detect cycle for different args"
  else
    return .passed

def run : IO TestRunner := do
  IO.println "  === Resolution State Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "empty_not_too_deep" (← testEmptyNotTooDeep)
  runner := runner.record "max_depth" (← testMaxDepth)
  runner := runner.record "push_pop_goals" (← testPushPopGoals)
  runner := runner.record "cycle_detection_primitive" (← testCycleDetectionPrimitive)
  runner := runner.record "no_false_positive_cycle" (← testNoCycleForDifferentArgs)

  return runner

end ResolutionStateTests

/-! ## Built-in Environment Tests -/

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
  let instances := env.getInstances BuiltinClass.eq
  -- Should have 8 instances (int, long, short, byte, float, double, bool, string)
  if instances.size >= 8 then
    return .passed
  else
    return .failed s!"Expected at least 8 Eq instances, got {instances.size}"

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

/-! ## Resolution Tests -/

namespace ResolutionTests

/-- Test: Resolve Eq Int succeeds -/
def testResolveEqInt : IO TestResult := do
  let ctx := TCContext.withDefaultInstances
  let action : TCM ResolutionResult := resolveInstance BuiltinClass.eq #[Value.vPrimTy .int]
  match action.run ctx with
  | .ok (result, _) =>
    if result.isFound then
      return .passed
    else
      return .failed s!"Resolution failed: {result}"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Resolve Show String succeeds -/
def testResolveShowString : IO TestResult := do
  let ctx := TCContext.withDefaultInstances
  let action : TCM ResolutionResult := resolveInstance BuiltinClass.show_ #[Value.vPrimTy .string]
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
  let action : TCM ResolutionResult := resolveInstance nonExistentClass #[Value.vPrimTy .int]
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
  let action : TCM ResolutionResult := resolveInstance BuiltinClass.num #[Value.vPrimTy .bool]
  match action.run ctx with
  | .ok (result, _) =>
    match result with
    | .notFound _ _ _ => return .passed
    | _ => return .failed s!"Expected notFound, got {result}"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Depth exceeded detection -/
def testDepthExceeded : IO TestResult := do
  let ctx := TCContext.withDefaultInstances
  -- Create a state that's already at max depth
  let state := { ResolutionState.empty with depth := 100 }
  let action : TCM ResolutionResult := resolveInstance BuiltinClass.eq #[Value.vPrimTy .int] state
  match action.run ctx with
  | .ok (result, _) =>
    match result with
    | .depthExceeded _ => return .passed
    | _ => return .failed s!"Expected depthExceeded, got {result}"
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
  runner := runner.record "resolve_show_string" (← testResolveShowString)
  runner := runner.record "resolve_non_existent_class" (← testResolveNonExistentClass)
  runner := runner.record "resolve_non_matching_type" (← testResolveNonMatchingType)
  runner := runner.record "depth_exceeded" (← testDepthExceeded)
  runner := runner.record "result_preserves_class_id" (← testResultPreservesClassId)

  return runner

end ResolutionTests

/-! ## TCContext Tests -/

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

/-! ## Main Test Runner -/

def run : IO TestRunner := do
  IO.println "=== Dependent Types Instance Tests (Phase 6) ==="
  IO.println ""

  let envRunner ← InstanceEnvTests.run
  envRunner.printSummary "Instance Environment"

  let stateRunner ← ResolutionStateTests.run
  stateRunner.printSummary "Resolution State"

  let builtinRunner ← BuiltinTests.run
  builtinRunner.printSummary "Built-in Environment"

  let resRunner ← ResolutionTests.run
  resRunner.printSummary "Resolution"

  let ctxRunner ← TCContextTests.run
  ctxRunner.printSummary "TCContext"

  IO.println ""

  let combined := envRunner.merge stateRunner |>.merge builtinRunner
    |>.merge resRunner |>.merge ctxRunner

  IO.println s!"Total: {combined.passed} passed, {combined.failed} failed"

  if combined.failed > 0 then
    IO.println ""
    IO.println "FAILURES:"
    for f in combined.failures do IO.println s!"  - {f}"

  return combined

end Test.Dependent.Instance
