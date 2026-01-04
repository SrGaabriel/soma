/-
  Test.Dependent.Usage - Unit tests for QTT usage checking (Phase 4)

  Tests cover:
  - Quantity compatibility checking
  - Linear variable usage enforcement
  - Erased variable restrictions
  - Usage snapshot operations
  - Branch usage checking
-/

import Soma.Dependent
import Soma.Metal.Expr
import Soma.Core
import Test.Fixtures

namespace Test.Dependent.Usage

open Soma.Dependent
open Soma.Dependent (CtxEntry TCContext)
open Soma.Core
open Soma.Metal (Expr ExprList Scope BindingId Name BinderInfo)
open Soma.Syntax (Span)
open Test.Fixtures

/-- Helper to create a dummy span -/
def testSpan : Span := Span.uninhabited

/-! ## Quantity Compatibility Tests

    usageCompatible(declared, actual) checks: actual ≤ declared
    This answers: "Is actual usage permitted given declared quantity?"

    For example:
    - usageCompatible(.omega, .one) checks if using once (1) is OK when ω is declared → true
    - usageCompatible(.one, .omega) checks if using many times (ω) is OK when 1 is declared → false
-/

namespace QuantityCompatTests

/-- Test: Zero actual usage is compatible with zero declared (erased var, not used) -/
def testZeroCompatZero : IO TestResult := do
  -- declared=0, actual=0: erased variable not used at runtime → OK
  if usageCompatible .zero .zero then return .passed
  else return .failed "actual=0 ≤ declared=0 should hold"

/-- Test: Zero actual usage is compatible with one declared (linear var, but unused is checked separately) -/
def testZeroCompatOne : IO TestResult := do
  -- declared=1, actual=0: 0 ≤ 1 in the semiring ordering
  -- NOTE: This only tests the ordering; linear vars need checkLinearBinding for exact-once enforcement
  if usageCompatible .one .zero then return .passed
  else return .failed "actual=0 ≤ declared=1 should hold (ordering only)"

/-- Test: Zero actual usage is compatible with omega declared (unrestricted, used zero times) -/
def testZeroCompatOmega : IO TestResult := do
  -- declared=ω, actual=0: not using an unrestricted var is fine
  if usageCompatible .omega .zero then return .passed
  else return .failed "actual=0 ≤ declared=ω should hold"

/-- Test: One actual usage is compatible with one declared (linear var used once) -/
def testOneCompatOne : IO TestResult := do
  -- declared=1, actual=1: linear variable used exactly once → OK
  if usageCompatible .one .one then return .passed
  else return .failed "actual=1 ≤ declared=1 should hold"

/-- Test: One actual usage is compatible with omega declared (unrestricted, used once) -/
def testOneCompatOmega : IO TestResult := do
  -- declared=ω, actual=1: using an unrestricted var once is fine
  if usageCompatible .omega .one then return .passed
  else return .failed "actual=1 ≤ declared=ω should hold"

/-- Test: Omega actual usage is compatible with omega declared (unrestricted, used many times) -/
def testOmegaCompatOmega : IO TestResult := do
  -- declared=ω, actual=ω: unrestricted variable used multiple times → OK
  if usageCompatible .omega .omega then return .passed
  else return .failed "actual=ω ≤ declared=ω should hold"

/-- Test: One actual usage is NOT compatible with zero declared (can't use erased var) -/
def testOneNotCompatZero : IO TestResult := do
  -- declared=0, actual=1: using an erased variable is forbidden
  if !usageCompatible .zero .one then return .passed
  else return .failed "actual=1 ≤ declared=0 should NOT hold"

/-- Test: Omega actual usage is NOT compatible with one declared (can't duplicate linear) -/
def testOmegaNotCompatOne : IO TestResult := do
  -- declared=1, actual=ω: using a linear variable multiple times is forbidden
  if !usageCompatible .one .omega then return .passed
  else return .failed "actual=ω ≤ declared=1 should NOT hold"

def run : IO TestRunner := do
  IO.println "  === Quantity Compatibility Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "zero_compat_zero" (← testZeroCompatZero)
  runner := runner.record "zero_compat_one" (← testZeroCompatOne)
  runner := runner.record "zero_compat_omega" (← testZeroCompatOmega)
  runner := runner.record "one_compat_one" (← testOneCompatOne)
  runner := runner.record "one_compat_omega" (← testOneCompatOmega)
  runner := runner.record "omega_compat_omega" (← testOmegaCompatOmega)
  runner := runner.record "one_not_compat_zero" (← testOneNotCompatZero)
  runner := runner.record "omega_not_compat_one" (← testOmegaNotCompatOne)

  return runner

end QuantityCompatTests

/-! ## Usage Snapshot Tests -/

namespace SnapshotTests

/-- Test: Empty snapshot has zero for all variables -/
def testEmptySnapshot : IO TestResult := do
  let snap := UsageSnapshot.empty
  if snap.get "x" == .zero then return .passed
  else return .failed "Empty snapshot should return zero"

/-- Test: Setting and getting usage -/
def testSetGet : IO TestResult := do
  let snap := UsageSnapshot.empty.set "x" .one
  if snap.get "x" == .one then return .passed
  else return .failed "Should get the set value"

/-- Test: Merge adds quantities -/
def testMerge : IO TestResult := do
  let s1 := UsageSnapshot.empty.set "x" .one
  let s2 := UsageSnapshot.empty.set "x" .one
  let merged := s1.merge s2
  -- 1 + 1 = ω
  if merged.get "x" == .omega then return .passed
  else return .failed s!"Expected omega, got {merged.get "x"}"

/-- Test: Join takes maximum -/
def testJoin : IO TestResult := do
  let s1 := UsageSnapshot.empty.set "x" .one
  let s2 := UsageSnapshot.empty.set "x" .omega
  let joined := s1.join s2
  -- max(1, ω) = ω
  if joined.get "x" == .omega then return .passed
  else return .failed s!"Expected omega, got {joined.get "x"}"

/-- Test: Join with zero and one gives one -/
def testJoinZeroOne : IO TestResult := do
  let s1 := UsageSnapshot.empty.set "x" .zero
  let s2 := UsageSnapshot.empty.set "x" .one
  let joined := s1.join s2
  if joined.get "x" == .one then return .passed
  else return .failed s!"Expected one, got {joined.get "x"}"

def run : IO TestRunner := do
  IO.println "  === Usage Snapshot Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "empty_snapshot" (← testEmptySnapshot)
  runner := runner.record "set_get" (← testSetGet)
  runner := runner.record "merge_adds" (← testMerge)
  runner := runner.record "join_takes_max" (← testJoin)
  runner := runner.record "join_zero_one" (← testJoinZeroOne)

  return runner

end SnapshotTests

/-! ## Linear Variable Tests -/

namespace LinearTests

/-- Test: Linear variable used exactly once is OK -/
def testLinearUsedOnce : IO TestResult := do
  let action : TCM Unit := do
    -- Add a linear binding
    TCM.withBinding "x" (.vPrimTy .int) .one .explicit testSpan do
      -- Use it once (use low-level API to record exact quantity)
      TCM.modifyState (·.useVar "x" .one)
      -- Check should pass
      checkLinearBinding "x" testSpan
  match action.run' with
  | .ok () => return .passed
  | .error e => return .failed s!"Should succeed: {e}"

/-- Test: Linear variable not used is an error -/
def testLinearNotUsed : IO TestResult := do
  let action : TCM Unit := do
    TCM.withBinding "x" (.vPrimTy .int) .one .explicit testSpan do
      -- Don't use it
      checkLinearBinding "x" testSpan
  match action.run with
  | .ok ((), state) =>
    -- Check for accumulated error
    if state.errors.any (fun e => match e with | .linearNotUsed "x" _ => true | _ => false)
    then return .passed
    else return .failed "Should have accumulated linearNotUsed error"
  | .error e =>
    match e with
    | .linearNotUsed name _ =>
      if name == "x" then return .passed
      else return .failed s!"Wrong variable: {name}"
    | _ => return .failed s!"Wrong error type: {e}"

/-- Test: Linear variable used multiple times is an error -/
def testLinearUsedMultiple : IO TestResult := do
  let action : TCM Unit := do
    TCM.withBinding "x" (.vPrimTy .int) .one .explicit testSpan do
      -- Use twice (1 + 1 = ω in QTT)
      TCM.modifyState (·.useVar "x" .one)
      TCM.modifyState (·.useVar "x" .one)
      checkLinearBinding "x" testSpan
  match action.run with
  | .ok ((), state) =>
    -- Check for accumulated error
    if state.errors.any (fun e => match e with | .quantityMismatch _ _ "x" _ => true | _ => false)
    then return .passed
    else return .failed "Should have accumulated quantityMismatch error"
  | .error e =>
    match e with
    | .quantityMismatch _ _ name _ =>
      if name == "x" then return .passed
      else return .failed s!"Wrong variable: {name}"
    | _ => return .failed s!"Wrong error type: {e}"

def run : IO TestRunner := do
  IO.println "  === Linear Variable Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "linear_used_once" (← testLinearUsedOnce)
  runner := runner.record "linear_not_used" (← testLinearNotUsed)
  runner := runner.record "linear_used_multiple" (← testLinearUsedMultiple)

  return runner

end LinearTests

/-! ## Erased Variable Tests -/

namespace ErasedTests

/-- Test: Erased variable used in erased context is OK -/
def testErasedInErasedContext : IO TestResult := do
  let action : TCM Unit := do
    TCM.withBinding "x" (.vPrimTy .int) .zero .explicit testSpan do
      -- When we bind with qty=0, we automatically enter erased context
      -- So this should succeed
      checkNotErased "x" testSpan
  match action.run' with
  | .ok () => return .passed
  | .error e => return .failed s!"Should succeed in erased context: {e}"

/-- Test: Erased variable from outer scope used at runtime is an error
    Note: We need to bind an erased var but NOT be inside it to test runtime usage -/
def testErasedAtRuntime : IO TestResult := do
  -- Create context with erased binding but not in erased mode
  let ctx := TCContext.empty
  let entry : CtxEntry := {
    name := "x", type := .vPrimTy .int, qty := .zero,
    level := ⟨0⟩, binder := .explicit, span := testSpan
  }
  -- Must populate both locals list AND localsByName HashMap for lookupLocal to work
  let ctx' := { ctx with locals := [entry], localsByName := ({} : Std.HashMap String CtxEntry).insert "x" entry }
  let action : TCM Unit := do
    checkNotErased "x" testSpan
  match action.run ctx' with
  | .ok _ => return .failed "Should have failed for erased var at runtime"
  | .error e =>
    match e with
    | .erasedUsedAtRuntime name _ _ =>
      if name == "x" then return .passed
      else return .failed s!"Wrong variable: {name}"
    | _ => return .failed s!"Wrong error type: {e}"

/-- Test: Non-erased variable at runtime is OK -/
def testNonErasedAtRuntime : IO TestResult := do
  let action : TCM Unit := do
    TCM.withBinding "x" (.vPrimTy .int) .omega .explicit testSpan do
      checkNotErased "x" testSpan
  match action.run' with
  | .ok () => return .passed
  | .error e => return .failed s!"Should succeed for non-erased var: {e}"

/-- Test: Binding with qty=0 automatically enters erased context -/
def testZeroBindingEntersErased : IO TestResult := do
  let action : TCM Bool := do
    TCM.withBinding "x" (.vPrimTy .int) .zero .explicit testSpan do
      TCM.isInErasedContext
  match action.run' with
  | .ok true => return .passed
  | .ok false => return .failed "Should be in erased context with qty=0 binding"
  | .error e => return .failed s!"Unexpected error: {e}"

def run : IO TestRunner := do
  IO.println "  === Erased Variable Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "erased_in_erased_context" (← testErasedInErasedContext)
  runner := runner.record "erased_at_runtime" (← testErasedAtRuntime)
  runner := runner.record "non_erased_at_runtime" (← testNonErasedAtRuntime)
  runner := runner.record "zero_binding_enters_erased" (← testZeroBindingEntersErased)

  return runner

end ErasedTests

/-! ## Checked Binding Tests -/

namespace CheckedBindingTests

/-- Test: withCheckedBinding for omega quantity (unrestricted) -/
def testOmegaBinding : IO TestResult := do
  let action : TCM Int := do
    withCheckedBinding "x" (.vPrimTy .int) .omega .explicit testSpan do
      -- Can use many times
      TCM.useVar "x" .omega
      TCM.useVar "x" .omega
      return 42
  match action.run' with
  | .ok 42 => return .passed
  | .ok n => return .failed s!"Wrong result: {n}"
  | .error e => return .failed s!"Should succeed: {e}"

/-- Test: withCheckedBinding for linear quantity (must use exactly once) -/
def testLinearBinding : IO TestResult := do
  let action : TCM Int := do
    withCheckedBinding "x" (.vPrimTy .int) .one .explicit testSpan do
      -- Use low-level API to record exact quantity
      TCM.modifyState (·.useVar "x" .one)
      return 42
  match action.run' with
  | .ok 42 => return .passed
  | .ok n => return .failed s!"Wrong result: {n}"
  | .error e => return .failed s!"Should succeed: {e}"

/-- Test: withCheckedBinding fails if linear not used -/
def testLinearBindingNotUsed : IO TestResult := do
  let action : TCM Int := do
    withCheckedBinding "x" (.vPrimTy .int) .one .explicit testSpan do
      return 42
  match action.run with
  | .ok (_, state) =>
    -- Check for accumulated error
    if state.errors.any (fun e => match e with | .linearNotUsed "x" _ => true | _ => false)
    then return .passed
    else return .failed "Should have accumulated linearNotUsed error"
  | .error (.linearNotUsed "x" _) => return .passed
  | .error e => return .failed s!"Wrong error: {e}"

def run : IO TestRunner := do
  IO.println "  === Checked Binding Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "omega_binding" (← testOmegaBinding)
  runner := runner.record "linear_binding" (← testLinearBinding)
  runner := runner.record "linear_binding_not_used" (← testLinearBindingNotUsed)

  return runner

end CheckedBindingTests

/-! ## useVarChecked Tests -/

namespace UseVarCheckedTests

/-- Test: useVarChecked records usage for non-erased var -/
def testUseVarCheckedRecords : IO TestResult := do
  let action : TCM Quantity := do
    TCM.withBinding "x" (.vPrimTy .int) .omega .explicit testSpan do
      useVarChecked "x" testSpan
      TCM.getUsage "x"
  match action.run' with
  | .ok qty =>
    if qty == .omega then return .passed
    else return .failed s!"Expected omega, got {qty}"
  | .error e => return .failed s!"Should succeed: {e}"

/-- Test: useVarChecked fails for erased var at runtime -/
def testUseVarCheckedErased : IO TestResult := do
  -- Create context with erased binding but not in erased mode
  let ctx := TCContext.empty
  let entry : CtxEntry := {
    name := "x", type := .vPrimTy .int, qty := .zero,
    level := ⟨0⟩, binder := .explicit, span := testSpan
  }
  -- Must populate both locals list AND localsByName HashMap for lookupLocal to work
  let ctx' := { ctx with locals := [entry], localsByName := ({} : Std.HashMap String CtxEntry).insert "x" entry }
  let action : TCM Unit := do
    useVarChecked "x" testSpan
  match action.run ctx' with
  | .ok _ => return .failed "Should have failed"
  | .error (.erasedUsedAtRuntime "x" _ _) => return .passed
  | .error e => return .failed s!"Wrong error: {e}"

/-- Test: useVarChecked in erased context allows erased vars -/
def testUseVarCheckedErasedContext : IO TestResult := do
  let action : TCM Unit := do
    TCM.withBinding "x" (.vPrimTy .int) .zero .explicit testSpan do
      inErasedScope do
        useVarChecked "x" testSpan
  match action.run' with
  | .ok () => return .passed
  | .error e => return .failed s!"Should succeed in erased context: {e}"

def run : IO TestRunner := do
  IO.println "  === useVarChecked Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "use_var_checked_records" (← testUseVarCheckedRecords)
  runner := runner.record "use_var_checked_erased" (← testUseVarCheckedErased)
  runner := runner.record "use_var_checked_erased_context" (← testUseVarCheckedErasedContext)

  return runner

end UseVarCheckedTests

/-! ## Function Usage Tests -/

namespace FunctionUsageTests

/-- Test: checkFunctionUsage with correctly used linear param -/
def testFunctionUsageLinearOK : IO TestResult := do
  let action : TCM Unit := do
    TCM.withBinding "x" (.vPrimTy .int) .one .explicit testSpan do
      -- Use low-level API to record exact quantity
      TCM.modifyState (·.useVar "x" .one)
      checkFunctionUsage [("x", .one, testSpan)]
  match action.run' with
  | .ok () => return .passed
  | .error e => return .failed s!"Should succeed: {e}"

/-- Test: checkFunctionUsage with unused linear param fails -/
def testFunctionUsageLinearUnused : IO TestResult := do
  let action : TCM Unit := do
    TCM.withBinding "x" (.vPrimTy .int) .one .explicit testSpan do
      checkFunctionUsage [("x", .one, testSpan)]
  match action.run with
  | .ok ((), state) =>
    -- Check for accumulated error
    if state.errors.any (fun e => match e with | .linearNotUsed "x" _ => true | _ => false)
    then return .passed
    else return .failed "Should have accumulated linearNotUsed error"
  | .error (.linearNotUsed "x" _) => return .passed
  | .error e => return .failed s!"Wrong error: {e}"

/-- Test: checkFunctionUsage with omega param allows any usage -/
def testFunctionUsageOmegaOK : IO TestResult := do
  let action : TCM Unit := do
    TCM.withBinding "x" (.vPrimTy .int) .omega .explicit testSpan do
      TCM.useVar "x" .omega
      TCM.useVar "x" .omega
      checkFunctionUsage [("x", .omega, testSpan)]
  match action.run' with
  | .ok () => return .passed
  | .error e => return .failed s!"Should succeed: {e}"

/-- Test: checkFunctionUsage with zero param allows no usage -/
def testFunctionUsageZeroOK : IO TestResult := do
  let action : TCM Unit := do
    TCM.withBinding "x" (.vPrimTy .int) .zero .explicit testSpan do
      checkFunctionUsage [("x", .zero, testSpan)]
  match action.run' with
  | .ok () => return .passed
  | .error e => return .failed s!"Should succeed: {e}"

def run : IO TestRunner := do
  IO.println "  === Function Usage Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "function_usage_linear_ok" (← testFunctionUsageLinearOK)
  runner := runner.record "function_usage_linear_unused" (← testFunctionUsageLinearUnused)
  runner := runner.record "function_usage_omega_ok" (← testFunctionUsageOmegaOK)
  runner := runner.record "function_usage_zero_ok" (← testFunctionUsageZeroOK)

  return runner

end FunctionUsageTests

/-! ## Main Test Runner -/

def run : IO TestRunner := do
  IO.println "=== Dependent Types Usage Tests (Phase 4) ==="
  IO.println ""

  let compatRunner ← QuantityCompatTests.run
  compatRunner.printSummary "Quantity Compatibility"

  let snapshotRunner ← SnapshotTests.run
  snapshotRunner.printSummary "Usage Snapshot"

  let linearRunner ← LinearTests.run
  linearRunner.printSummary "Linear Variables"

  let erasedRunner ← ErasedTests.run
  erasedRunner.printSummary "Erased Variables"

  let checkedBindingRunner ← CheckedBindingTests.run
  checkedBindingRunner.printSummary "Checked Bindings"

  let useVarCheckedRunner ← UseVarCheckedTests.run
  useVarCheckedRunner.printSummary "useVarChecked"

  let functionUsageRunner ← FunctionUsageTests.run
  functionUsageRunner.printSummary "Function Usage"

  IO.println ""

  let combined := compatRunner.merge snapshotRunner |>.merge linearRunner
    |>.merge erasedRunner |>.merge checkedBindingRunner
    |>.merge useVarCheckedRunner |>.merge functionUsageRunner

  IO.println s!"Total: {combined.passed} passed, {combined.failed} failed"

  if combined.failed > 0 then
    IO.println ""
    IO.println "FAILURES:"
    for f in combined.failures do IO.println s!"  - {f}"

  return combined

end Test.Dependent.Usage
