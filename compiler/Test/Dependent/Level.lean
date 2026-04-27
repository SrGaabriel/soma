import Soma.Dependent
import Soma.Core
import Test.Fixtures

namespace Test.Dependent.Level

open Soma.Dependent
open Soma.Core
open Test.Fixtures

private def runTCM (action : TCM α) : IO (Except TCError α) := do
  match action.run TCContext.empty TCState.empty with
  | .ok (a, _) => return .ok a
  | .error e => return .error e

/-- Drain to fixpoint, then read back the solution for a level variable -/
private def solveOne (action : TCM Unit) (id : LevelVarId) : TCM Level := do
  action
  drainConstraints
  TCM.zonkLevel (.var id)

/-- Test: `?u = lit 1` solves to lit 1 -/
def testSingleEq : IO TestResult := do
  match ← runTCM do
    let u ← TCM.freshLevelVar "u"
    solveOne (TCM.postpone (.levelEq (.var u) (.lit 1))) u
  with
  | .ok (.lit 1) => return .passed
  | .ok l        => return .failed s!"expected lit 1, got {l}"
  | .error e     => return .failed s!"unexpected error: {e}"

/-- Test: chain `?u = ?v`, `?v = lit 2` resolves both to 2 -/
def testChainEq : IO TestResult := do
  match ← runTCM do
    let u ← TCM.freshLevelVar "u"
    let v ← TCM.freshLevelVar "v"
    TCM.postpone (.levelEq (.var u) (.var v))
    TCM.postpone (.levelEq (.var v) (.lit 2))
    drainConstraints
    return (← TCM.zonkLevel (.var u), ← TCM.zonkLevel (.var v))
  with
  | .ok (.lit 2, .lit 2) => return .passed
  | .ok (a, b)           => return .failed s!"expected (2,2), got ({a}, {b})"
  | .error e             => return .failed s!"unexpected error: {e}"

/-- Test: `?u ≤ lit 5` defaults `?u` to a value ≤ 5 -/
def testLeBound : IO TestResult := do
  match ← runTCM do
    let u ← TCM.freshLevelVar "u"
    solveOne (TCM.postpone (.levelLe (.var u) (.lit 5))) u
  with
  | .ok (.lit n) =>
    if n ≤ 5 then return .passed
    else return .failed s!"expected ≤ 5, got {n}"
  | .ok other  => return .failed s!"expected literal, got {other}"
  | .error e   => return .failed s!"unexpected error: {e}"

/-- Test: conflicting equalities surface a unification failure -/
def testConflict : IO TestResult := do
  let result ← runTCM do
    let u ← TCM.freshLevelVar "u"
    TCM.postpone (.levelEq (.var u) (.lit 1))
    TCM.postpone (.levelEq (.var u) (.lit 2))
    drainConstraints
    let state ← TCM.getState
    return state.errors.size
  match result with
  | .ok n =>
    if n > 0 then return .passed
    else return .failed "expected an error to be recorded"
  | .error _ => return .passed

def run : IO TestRunner := do
  IO.println "=== Level Inference Integration Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "single_eq" (← testSingleEq)
  runner := runner.record "chain_eq" (← testChainEq)
  runner := runner.record "le_bound" (← testLeBound)
  runner := runner.record "conflict" (← testConflict)
  return runner

end Test.Dependent.Level
