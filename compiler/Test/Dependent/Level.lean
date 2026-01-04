/-
  Test.Dependent.Level - Unit tests for Universe Level Inference (Phase 5)

  Tests cover:
  - Level constraint solving (equality, ordering, max)
  - Solution substitution
  - Defaulting unsolved variables to 0
  - TCM integration
-/

import Soma.Dependent
import Soma.Core
import Test.Fixtures

namespace Test.Dependent.Level

open Soma.Dependent
open Soma.Core
open Test.Fixtures

/-! ## Level Constraint Solving Tests -/

namespace SolveEqTests

/-- Test: Two equal literals are satisfied -/
def testLitEqLit : IO TestResult := do
  let solutions : Std.HashMap Nat Level := {}
  match solveEq solutions (.lit 0) (.lit 0) with
  | .satisfied => return .passed
  | r => return .failed s!"Expected satisfied, got {repr r}"

/-- Test: Two unequal literals are unsatisfiable -/
def testLitNeqLit : IO TestResult := do
  let solutions : Std.HashMap Nat Level := {}
  match solveEq solutions (.lit 0) (.lit 1) with
  | .unsatisfiable _ => return .passed
  | r => return .failed s!"Expected unsatisfiable, got {repr r}"

/-- Test: Variable equals literal gets solved -/
def testVarEqLit : IO TestResult := do
  let solutions : Std.HashMap Nat Level := {}
  let varId : LevelVarId := ⟨0, "u"⟩
  match solveEq solutions (.var varId) (.lit 1) with
  | .solved [(0, .lit 1)] => return .passed
  | .solved sols => return .failed s!"Wrong solution: {repr sols}"
  | r => return .failed s!"Expected solved, got {repr r}"

/-- Test: Literal equals variable gets solved -/
def testLitEqVar : IO TestResult := do
  let solutions : Std.HashMap Nat Level := {}
  let varId : LevelVarId := ⟨0, "u"⟩
  match solveEq solutions (.lit 2) (.var varId) with
  | .solved [(0, .lit 2)] => return .passed
  | .solved sols => return .failed s!"Wrong solution: {repr sols}"
  | r => return .failed s!"Expected solved, got {repr r}"

/-- Test: Same variable on both sides is satisfied -/
def testVarEqSameVar : IO TestResult := do
  let solutions : Std.HashMap Nat Level := {}
  let varId : LevelVarId := ⟨0, "u"⟩
  match solveEq solutions (.var varId) (.var varId) with
  | .satisfied => return .passed
  | r => return .failed s!"Expected satisfied, got {repr r}"

/-- Test: Solved variable gets substituted -/
def testSolvedVarSubst : IO TestResult := do
  let solutions : Std.HashMap Nat Level := ({} : Std.HashMap Nat Level).insert 0 (.lit 1)
  let varId : LevelVarId := ⟨0, "u"⟩
  match solveEq solutions (.var varId) (.lit 1) with
  | .satisfied => return .passed
  | r => return .failed s!"Expected satisfied after substitution, got {repr r}"

def run : IO TestRunner := do
  IO.println "  === Level Equality Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "lit_eq_lit" (← testLitEqLit)
  runner := runner.record "lit_neq_lit" (← testLitNeqLit)
  runner := runner.record "var_eq_lit" (← testVarEqLit)
  runner := runner.record "lit_eq_var" (← testLitEqVar)
  runner := runner.record "var_eq_same_var" (← testVarEqSameVar)
  runner := runner.record "solved_var_subst" (← testSolvedVarSubst)

  return runner

end SolveEqTests

/-! ## Level Ordering Tests -/

namespace SolveLeTests

/-- Test: 0 ≤ 0 is satisfied -/
def testZeroLeZero : IO TestResult := do
  let solutions : Std.HashMap Nat Level := {}
  match solveLe solutions (.lit 0) (.lit 0) with
  | .satisfied => return .passed
  | r => return .failed s!"Expected satisfied, got {repr r}"

/-- Test: 0 ≤ 1 is satisfied -/
def testZeroLeOne : IO TestResult := do
  let solutions : Std.HashMap Nat Level := {}
  match solveLe solutions (.lit 0) (.lit 1) with
  | .satisfied => return .passed
  | r => return .failed s!"Expected satisfied, got {repr r}"

/-- Test: 1 > 0 is unsatisfiable -/
def testOneGtZero : IO TestResult := do
  let solutions : Std.HashMap Nat Level := {}
  match solveLe solutions (.lit 1) (.lit 0) with
  | .unsatisfiable _ => return .passed
  | r => return .failed s!"Expected unsatisfiable, got {repr r}"

/-- Test: var ≤ lit gives minimal solution (0) -/
def testVarLeLit : IO TestResult := do
  let solutions : Std.HashMap Nat Level := {}
  let varId : LevelVarId := ⟨0, "u"⟩
  match solveLe solutions (.var varId) (.lit 5) with
  | .solved [(0, .lit 0)] => return .passed
  | .solved sols => return .failed s!"Expected 0, got {repr sols}"
  | r => return .failed s!"Expected solved, got {repr r}"

/-- Test: lit ≤ var solves var to at least that value -/
def testLitLeVar : IO TestResult := do
  let solutions : Std.HashMap Nat Level := {}
  let varId : LevelVarId := ⟨0, "u"⟩
  match solveLe solutions (.lit 3) (.var varId) with
  | .solved [(0, .lit 3)] => return .passed
  | .solved sols => return .failed s!"Expected 3, got {repr sols}"
  | r => return .failed s!"Expected solved, got {repr r}"

/-- Test: same var ≤ same var is satisfied -/
def testVarLeSameVar : IO TestResult := do
  let solutions : Std.HashMap Nat Level := {}
  let varId : LevelVarId := ⟨0, "u"⟩
  match solveLe solutions (.var varId) (.var varId) with
  | .satisfied => return .passed
  | r => return .failed s!"Expected satisfied, got {repr r}"

def run : IO TestRunner := do
  IO.println "  === Level Ordering Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "zero_le_zero" (← testZeroLeZero)
  runner := runner.record "zero_le_one" (← testZeroLeOne)
  runner := runner.record "one_gt_zero" (← testOneGtZero)
  runner := runner.record "var_le_lit" (← testVarLeLit)
  runner := runner.record "lit_le_var" (← testLitLeVar)
  runner := runner.record "var_le_same_var" (← testVarLeSameVar)

  return runner

end SolveLeTests

/-! ## Max Constraint Tests -/

namespace SolveMaxTests

/-- Test: max(0, 0) = 0 is satisfied -/
def testMaxZeroZero : IO TestResult := do
  let solutions : Std.HashMap Nat Level := {}
  match solveMaxEq solutions (.lit 0) (.lit 0) (.lit 0) with
  | .satisfied => return .passed
  | r => return .failed s!"Expected satisfied, got {repr r}"

/-- Test: max(1, 2) = 2 is satisfied -/
def testMaxOneTwo : IO TestResult := do
  let solutions : Std.HashMap Nat Level := {}
  match solveMaxEq solutions (.lit 1) (.lit 2) (.lit 2) with
  | .satisfied => return .passed
  | r => return .failed s!"Expected satisfied, got {repr r}"

/-- Test: max(1, 2) = 1 is unsatisfiable -/
def testMaxOneTwoWrong : IO TestResult := do
  let solutions : Std.HashMap Nat Level := {}
  match solveMaxEq solutions (.lit 1) (.lit 2) (.lit 1) with
  | .unsatisfiable _ => return .passed
  | r => return .failed s!"Expected unsatisfiable, got {repr r}"

/-- Test: max(1, 2) = ?u solves ?u to 2 -/
def testMaxSolveResult : IO TestResult := do
  let solutions : Std.HashMap Nat Level := {}
  let varId : LevelVarId := ⟨0, "u"⟩
  match solveMaxEq solutions (.lit 1) (.lit 2) (.var varId) with
  | .solved [(0, .lit 2)] => return .passed
  | .solved sols => return .failed s!"Expected 2, got {repr sols}"
  | r => return .failed s!"Expected solved, got {repr r}"

/-- Test: max(0, l) = ?u solves ?u to l -/
def testMaxZeroL : IO TestResult := do
  let solutions : Std.HashMap Nat Level := {}
  let varId0 : LevelVarId := ⟨0, "u"⟩
  let varId1 : LevelVarId := ⟨1, "v"⟩
  match solveMaxEq solutions (.lit 0) (.var varId1) (.var varId0) with
  | .solved [(0, .var ⟨1, "v"⟩)] => return .passed
  | .solved sols => return .failed s!"Expected var 1, got {repr sols}"
  | r => return .failed s!"Expected solved, got {repr r}"

def run : IO TestRunner := do
  IO.println "  === Max Constraint Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "max_zero_zero" (← testMaxZeroZero)
  runner := runner.record "max_one_two" (← testMaxOneTwo)
  runner := runner.record "max_one_two_wrong" (← testMaxOneTwoWrong)
  runner := runner.record "max_solve_result" (← testMaxSolveResult)
  runner := runner.record "max_zero_l" (← testMaxZeroL)

  return runner

end SolveMaxTests

/-! ## Full Solver Tests -/

namespace SolverTests

/-- Test: Empty constraints give empty solutions -/
def testEmptyConstraints : IO TestResult := do
  match solveLevelConstraints #[] with
  | .ok sols =>
    if sols.isEmpty then return .passed
    else return .failed s!"Expected empty, got {sols.size} solutions"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Single equality constraint -/
def testSingleEq : IO TestResult := do
  let varId : LevelVarId := ⟨0, "u"⟩
  let constraints := #[LevelConstraintInfo.eq (.var varId) (.lit 1)]
  match solveLevelConstraints constraints with
  | .ok sols =>
    match sols.get? 0 with
    | some (.lit 1) => return .passed
    | some l => return .failed s!"Expected lit 1, got {l}"
    | none => return .failed "Variable not solved"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Chain of equalities - ?u = ?v and ?v = 2 should resolve ?u to 2 via substitution -/
def testChainEq : IO TestResult := do
  let u : LevelVarId := ⟨0, "u"⟩
  let v : LevelVarId := ⟨1, "v"⟩
  let constraints := #[
    LevelConstraintInfo.eq (.var u) (.var v),
    LevelConstraintInfo.eq (.var v) (.lit 2)
  ]
  match solveLevelConstraints constraints with
  | .ok sols =>
    -- Apply substitution to get final values
    let uFinal := applyLevelSolutions sols (.var u)
    let vFinal := applyLevelSolutions sols (.var v)
    match uFinal, vFinal with
    | .lit 2, .lit 2 => return .passed
    | l1, l2 => return .failed s!"Expected (2, 2), got ({l1}, {l2})"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Unsolved variables default to 0 -/
def testDefaultToZero : IO TestResult := do
  let u : LevelVarId := ⟨0, "u"⟩
  let v : LevelVarId := ⟨1, "v"⟩
  -- u ≤ v with no other info - both should default to 0
  let constraints := #[LevelConstraintInfo.le (.var u) (.var v)]
  match solveLevelConstraints constraints with
  | .ok sols =>
    -- Apply substitution to get final values
    let uFinal := applyLevelSolutions sols (.var u)
    let vFinal := applyLevelSolutions sols (.var v)
    match uFinal, vFinal with
    | .lit 0, .lit 0 => return .passed
    | l1, l2 => return .failed s!"Expected (0, 0), got ({l1}, {l2})"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Conflicting constraints give error -/
def testConflict : IO TestResult := do
  let u : LevelVarId := ⟨0, "u"⟩
  let constraints := #[
    LevelConstraintInfo.eq (.var u) (.lit 1),
    LevelConstraintInfo.eq (.var u) (.lit 2)
  ]
  match solveLevelConstraints constraints with
  | .ok _ => return .failed "Expected error for conflicting constraints"
  | .error _ => return .passed

def run : IO TestRunner := do
  IO.println "  === Full Solver Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "empty_constraints" (← testEmptyConstraints)
  runner := runner.record "single_eq" (← testSingleEq)
  runner := runner.record "chain_eq" (← testChainEq)
  runner := runner.record "default_to_zero" (← testDefaultToZero)
  runner := runner.record "conflict" (← testConflict)

  return runner

end SolverTests

/-! ## Level Substitution Tests -/

namespace SubstTests

/-- Test: Literal unchanged -/
def testLitUnchanged : IO TestResult := do
  let solutions : Std.HashMap Nat Level := {}
  let result := applyLevelSolutions solutions (.lit 5)
  if result == .lit 5 then return .passed
  else return .failed s!"Expected lit 5, got {result}"

/-- Test: Solved variable gets substituted -/
def testVarSubst : IO TestResult := do
  let solutions : Std.HashMap Nat Level := ({} : Std.HashMap Nat Level).insert 0 (.lit 3)
  let varId : LevelVarId := ⟨0, "u"⟩
  let result := applyLevelSolutions solutions (.var varId)
  if result == .lit 3 then return .passed
  else return .failed s!"Expected lit 3, got {result}"

/-- Test: Unsolved variable unchanged -/
def testUnsolvedVar : IO TestResult := do
  let solutions : Std.HashMap Nat Level := {}
  let varId : LevelVarId := ⟨0, "u"⟩
  let result := applyLevelSolutions solutions (.var varId)
  if result == .var varId then return .passed
  else return .failed s!"Expected var unchanged, got {result}"

/-- Test: Max gets simplified after substitution -/
def testMaxSimplify : IO TestResult := do
  let solutions : Std.HashMap Nat Level := ({} : Std.HashMap Nat Level).insert 0 (.lit 2)
  let varId : LevelVarId := ⟨0, "u"⟩
  let result := applyLevelSolutions solutions (Level.mkMax (.var varId) (.lit 3))
  if result == .lit 3 then return .passed
  else return .failed s!"Expected lit 3, got {result}"

/-- Test: Succ gets simplified after substitution -/
def testSuccSimplify : IO TestResult := do
  let solutions : Std.HashMap Nat Level := ({} : Std.HashMap Nat Level).insert 0 (.lit 1)
  let varId : LevelVarId := ⟨0, "u"⟩
  let result := applyLevelSolutions solutions (Level.mkSucc (.var varId))
  if result == .lit 2 then return .passed
  else return .failed s!"Expected lit 2, got {result}"

def run : IO TestRunner := do
  IO.println "  === Level Substitution Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "lit_unchanged" (← testLitUnchanged)
  runner := runner.record "var_subst" (← testVarSubst)
  runner := runner.record "unsolved_var" (← testUnsolvedVar)
  runner := runner.record "max_simplify" (← testMaxSimplify)
  runner := runner.record "succ_simplify" (← testSuccSimplify)

  return runner

end SubstTests

/-! ## TCM Integration Tests -/

namespace TCMTests

/-- Test: freshType creates Type with fresh level var -/
def testFreshType : IO TestResult := do
  let action : TCM Value := freshType "test"
  match action.run' with
  | .ok (.vType (.var ⟨0, "test"⟩)) => return .passed
  | .ok (.vType _) => return .failed "Expected vType with var id 0"
  | .ok _ => return .failed "Expected vType"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: assertType succeeds on Type -/
def testAssertTypeOk : IO TestResult := do
  let action : TCM Level := assertType (.vType (.lit 1))
  match action.run' with
  | .ok (.lit 1) => return .passed
  | .ok l => return .failed s!"Expected lit 1, got {l}"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: assertType fails on non-Type -/
def testAssertTypeFail : IO TestResult := do
  let action : TCM Level := assertType (.vPrimTy .int)
  match action.run' with
  | .ok _ => return .failed "Expected error for non-Type"
  | .error _ => return .passed

/-- Test: piTypeLevel computes max -/
def testPiTypeLevel : IO TestResult := do
  let result := piTypeLevel (.lit 1) (.lit 2)
  if result == .lit 2 then return .passed
  else return .failed s!"Expected 2, got {result}"

/-- Test: sigmaTypeLevel computes max -/
def testSigmaTypeLevel : IO TestResult := do
  let result := sigmaTypeLevel (.lit 3) (.lit 1)
  if result == .lit 3 then return .passed
  else return .failed s!"Expected 3, got {result}"

def run : IO TestRunner := do
  IO.println "  === TCM Integration Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "fresh_type" (← testFreshType)
  runner := runner.record "assert_type_ok" (← testAssertTypeOk)
  runner := runner.record "assert_type_fail" (← testAssertTypeFail)
  runner := runner.record "pi_type_level" (← testPiTypeLevel)
  runner := runner.record "sigma_type_level" (← testSigmaTypeLevel)

  return runner

end TCMTests

/-! ## Main Test Runner -/

def run : IO TestRunner := do
  IO.println "=== Dependent Types Level Tests (Phase 5) ==="
  IO.println ""

  let eqRunner ← SolveEqTests.run
  eqRunner.printSummary "Level Equality"

  let leRunner ← SolveLeTests.run
  leRunner.printSummary "Level Ordering"

  let maxRunner ← SolveMaxTests.run
  maxRunner.printSummary "Max Constraints"

  let solverRunner ← SolverTests.run
  solverRunner.printSummary "Full Solver"

  let substRunner ← SubstTests.run
  substRunner.printSummary "Level Substitution"

  let tcmRunner ← TCMTests.run
  tcmRunner.printSummary "TCM Integration"

  IO.println ""

  let combined := eqRunner.merge leRunner |>.merge maxRunner
    |>.merge solverRunner |>.merge substRunner |>.merge tcmRunner

  IO.println s!"Total: {combined.passed} passed, {combined.failed} failed"

  if combined.failed > 0 then
    IO.println ""
    IO.println "FAILURES:"
    for f in combined.failures do IO.println s!"  - {f}"

  return combined

end Test.Dependent.Level
