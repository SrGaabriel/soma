/-
  Soma.Dependent.Level - Universe Level Inference and Constraint Solving

  This module implements universe level inference for dependent types.
  The goal is to infer universe levels so users can write `Type` instead
  of `Type₀`, `Type₁`, etc.

  Strategy:
  1. Create fresh level variables when user writes `Type`
  2. Collect constraints during type checking (equality, ordering, max)
  3. Solve constraints after checking completes
  4. Default unsolved level variables to 0

  Key invariant: Type_i : Type_(i+1)
  For Π-types and Σ-types: if A : Type_i and B : Type_j, then (x:A) → B : Type_(max i j)
-/

import Soma.Core.Level
import Soma.Dependent.Monad
import Soma.Dependent.Error
import Soma.Dependent.Convert

namespace Soma.Dependent

open Soma.Core

/-- Extended level constraint with source information -/
structure LevelConstraintInfo where
  /-- The constraint itself -/
  constraint : Level.LevelConstraint
  /-- Why this constraint was generated -/
  reason : String := ""
  deriving Repr

namespace LevelConstraintInfo

def eq (l1 l2 : Level) (reason : String := "") : LevelConstraintInfo :=
  ⟨.eq l1 l2, reason⟩

def le (l1 l2 : Level) (reason : String := "") : LevelConstraintInfo :=
  ⟨.le l1 l2, reason⟩

def maxEq (l1 l2 result : Level) (reason : String := "") : LevelConstraintInfo :=
  ⟨.maxEq l1 l2 result, reason⟩

end LevelConstraintInfo

/-- Apply current solutions to a level -/
partial def applyLevelSolutions (solutions : Std.HashMap Nat Level) (l : Level) : Level :=
  match l with
  | .lit n => .lit n
  | .var v =>
    match solutions.get? v.id with
    | some l' => applyLevelSolutions solutions l'  -- Recursively apply
    | none => .var v
  | .max l1 l2 =>
    Level.mkMax (applyLevelSolutions solutions l1) (applyLevelSolutions solutions l2)
  | .succ l' =>
    Level.mkSucc (applyLevelSolutions solutions l')

/-- Result of trying to solve a single constraint -/
inductive SolveResult where
  /-- Constraint was solved, possibly generating new solutions -/
  | solved (newSolutions : List (Nat × Level))
  /-- Constraint is already satisfied -/
  | satisfied
  /-- Constraint cannot be solved yet (needs more information) -/
  | deferred
  /-- Constraint is unsatisfiable -/
  | unsatisfiable (reason : String)
  deriving Repr

/-- Try to solve a level equality constraint: l1 = l2 -/
def solveEq (solutions : Std.HashMap Nat Level) (l1 l2 : Level) : SolveResult :=
  let l1' := applyLevelSolutions solutions l1 |>.simplify
  let l2' := applyLevelSolutions solutions l2 |>.simplify
  -- Check for syntactic equality first (handles reflexive case like ?u = ?u)
  if l1' == l2' then .satisfied
  else match l1', l2' with
  -- Both concrete and equal
  | .lit n1, .lit n2 =>
    if n1 == n2 then .satisfied
    else .unsatisfiable s!"level {n1} ≠ {n2}"
  -- Variable on left, solve it
  | .var v, rhs =>
    if rhs.freeVars.any (·.id == v.id) then
      .unsatisfiable s!"occurs check: {v} occurs in {rhs}"
    else
      .solved [(v.id, rhs)]
  -- Variable on right, solve it
  | lhs, .var v =>
    if lhs.freeVars.any (·.id == v.id) then
      .unsatisfiable s!"occurs check: {v} occurs in {lhs}"
    else
      .solved [(v.id, lhs)]
  -- Can't solve yet
  | _, _ => .deferred

/-- Try to solve a level ordering constraint: l1 ≤ l2 -/
def solveLe (solutions : Std.HashMap Nat Level) (l1 l2 : Level) : SolveResult :=
  let l1' := applyLevelSolutions solutions l1 |>.simplify
  let l2' := applyLevelSolutions solutions l2 |>.simplify
  match l1', l2' with
  -- Both concrete
  | .lit n1, .lit n2 =>
    if n1 ≤ n2 then .satisfied
    else .unsatisfiable s!"level {n1} > {n2}"
  -- 0 ≤ anything
  | .lit 0, _ => .satisfied
  -- Variable ≤ concrete: solve variable to 0 (minimal solution)
  | .var v, .lit _ =>
    .solved [(v.id, .lit 0)]  -- Minimal satisfying assignment
  -- Concrete ≤ variable: solve variable to at least that value
  | .lit n, .var v =>
    .solved [(v.id, .lit n)]  -- Minimal satisfying assignment
  -- Same variable on both sides
  | .var v1, .var v2 =>
    if v1.id == v2.id then .satisfied
    else .deferred
  -- Can't solve yet
  | _, _ => .deferred

/-- Try to solve a max constraint: max(l1, l2) = result -/
def solveMaxEq (solutions : Std.HashMap Nat Level) (l1 l2 result : Level) : SolveResult :=
  let l1' := applyLevelSolutions solutions l1 |>.simplify
  let l2' := applyLevelSolutions solutions l2 |>.simplify
  let result' := applyLevelSolutions solutions result |>.simplify
  match l1', l2', result' with
  -- All concrete
  | .lit n1, .lit n2, .lit r =>
    if Nat.max n1 n2 == r then .satisfied
    else .unsatisfiable s!"max({n1}, {n2}) = {Nat.max n1 n2} ≠ {r}"
  -- Result is a variable, solve it
  | .lit n1, .lit n2, .var v =>
    .solved [(v.id, .lit (Nat.max n1 n2))]
  -- One side is 0
  | .lit 0, l, .var v =>
    .solved [(v.id, l)]
  | l, .lit 0, .var v =>
    .solved [(v.id, l)]
  -- Both sides same
  | l, l', .var v =>
    if l == l' then .solved [(v.id, l)]
    else .deferred
  -- Can't solve yet
  | _, _, _ => .deferred

/-- Try to solve a single level constraint -/
def solveLevelConstraint (solutions : Std.HashMap Nat Level)
    (c : Level.LevelConstraint) : SolveResult :=
  match c with
  | .eq l1 l2 => solveEq solutions l1 l2
  | .le l1 l2 => solveLe solutions l1 l2
  | .maxEq l1 l2 r => solveMaxEq solutions l1 l2 r

/-- Default maximum iterations for the constraint solver -/
def defaultMaxIterations : Nat := 100

/-- Configuration for the level constraint solver -/
structure LevelSolverConfig where
  /-- Maximum iterations before giving up -/
  maxIterations : Nat := defaultMaxIterations
  deriving Inhabited

/-- Solver state passed through iteration -/
structure SolverState where
  solutions : Std.HashMap Nat Level
  constraints : List LevelConstraintInfo
  errors : List String
  deriving Inhabited

/-- Process one constraint and return updated state -/
def processConstraint (c : LevelConstraintInfo) (st : SolverState)
    : SolverState × Bool := -- returns (newState, madeProgress)
  match solveLevelConstraint st.solutions c.constraint with
  | .solved newSols =>
    let newSolutions := newSols.foldl (fun acc (k, v) => acc.insert k v) st.solutions
    ({ st with solutions := newSolutions }, true)
  | .satisfied =>
    (st, true)  -- Made progress by eliminating constraint
  | .deferred =>
    ({ st with constraints := c :: st.constraints }, false)
  | .unsatisfiable reason =>
    ({ st with errors := s!"Level constraint unsatisfiable: {reason}" :: st.errors }, false)

/-- Process all constraints in one iteration -/
def processAllConstraints (constraints : List LevelConstraintInfo) (st : SolverState)
    : SolverState × Bool :=
  constraints.foldl (fun (acc, progress) c =>
    let (newSt, made) := processConstraint c { acc with constraints := acc.constraints }
    ({ newSt with constraints := newSt.constraints }, progress || made)
  ) ({ st with constraints := [] }, false)

/-- Run solver iterations until fixpoint or max iterations -/
partial def solveLoop (fuel : Nat) (st : SolverState) : SolverState :=
  if fuel == 0 then st
  else if st.constraints.isEmpty then st
  else
    let (newSt, madeProgress) := processAllConstraints st.constraints { st with constraints := [] }
    if !madeProgress then newSt
    else solveLoop (fuel - 1) newSt

/-- Run solver with configuration -/
def solveLoopWithConfig (config : LevelSolverConfig) (st : SolverState) : SolverState :=
  solveLoop config.maxIterations st

/-- Default all remaining level variables to 0 -/
def defaultUnsolved (constraints : List LevelConstraintInfo) (solutions : Std.HashMap Nat Level)
    : Std.HashMap Nat Level :=
  let allVars := constraints.foldl (fun acc c =>
    match c.constraint with
    | .eq l1 l2 => acc ++ l1.freeVarsUnique ++ l2.freeVarsUnique
    | .le l1 l2 => acc ++ l1.freeVarsUnique ++ l2.freeVarsUnique
    | .maxEq l1 l2 r => acc ++ l1.freeVarsUnique ++ l2.freeVarsUnique ++ r.freeVarsUnique
  ) []
  allVars.foldl (fun acc v =>
    if acc.get? v.id |>.isNone then acc.insert v.id (.lit 0)
    else acc
  ) solutions

/-- Solve all level constraints, returning solutions or an error -/
def solveLevelConstraints (constraints : Array LevelConstraintInfo)
    (config : LevelSolverConfig := {}) : Except String (Std.HashMap Nat Level) :=
  let initialState : SolverState := {
    solutions := {}
    constraints := constraints.toList
    errors := []
  }
  let finalState := solveLoopWithConfig config initialState
  if !finalState.errors.isEmpty then
    .error (String.intercalate "\n" finalState.errors.reverse)
  else
    let finalSolutions := defaultUnsolved finalState.constraints finalState.solutions
    .ok finalSolutions

/-- Add a level equality constraint -/
def addLevelEq (l1 l2 : Level) : TCM Unit := do
  TCM.postpone (.levelEq l1 l2)

/-- Add a level ordering constraint -/
def addLevelLe (l1 l2 : Level) : TCM Unit := do
  TCM.postpone (.levelLe l1 l2)

/-- Collect level constraints from postponed constraints -/
def collectLevelConstraints : TCM (Array LevelConstraintInfo) := do
  let postponed ← TCM.getPostponed
  let mut levelConstraints : Array LevelConstraintInfo := #[]
  for c in postponed do
    match c with
    | .levelEq l1 l2 =>
      levelConstraints := levelConstraints.push (LevelConstraintInfo.eq l1 l2)
    | .levelLe l1 l2 =>
      levelConstraints := levelConstraints.push (LevelConstraintInfo.le l1 l2)
    | _ => pure ()  -- Skip non-level constraints
  return levelConstraints

/-- Solve level constraints and apply solutions to the state -/
def solveLevels : TCM Unit := do
  let constraints ← collectLevelConstraints
  if constraints.isEmpty then return

  match solveLevelConstraints constraints with
  | .ok solutions =>
    -- Store solutions in state
    let state ← TCM.getState
    -- Merge new solutions into existing level solutions
    let newLevelSolutions := solutions.toList.foldl (init := state.levelSolutions) fun acc (k, v) =>
      acc.insert k v
    TCM.modifyState fun s => { s with levelSolutions := newLevelSolutions }
  | .error _ =>
    -- Create a unification failure for level mismatch
    let span ← TCM.getSpan
    TCM.addError (.unificationFailed (.levelMismatch .zero .one) .general span #[] #[])

/-- Apply level solutions to a level -/
def solveLevelVars (l : Level) : TCM Level := do
  let state ← TCM.getState
  let solutions := state.levelSolutions
  return applyLevelSolutions solutions l

/-- Apply level solutions to a Value -/
partial def zonkValueLevels (v : Value) : TCM Value := do
  match v with
  | .vType l =>
    let l' ← solveLevelVars l
    return .vType l'
  | .vPi qty binder name dom cod =>
    let dom' ← zonkValueLevels dom
    -- Closures contain terms, not values with levels, so skip
    return .vPi qty binder name dom' cod
  | .vLam name body =>
    return .vLam name body
  | .vSigma qty name fst snd =>
    let fst' ← zonkValueLevels fst
    return .vSigma qty name fst' snd
  | .vPair fst snd =>
    let fst' ← zonkValueLevels fst
    let snd' ← zonkValueLevels snd
    return Value.vPair fst' snd'
  | .vNeutral ty neu =>
    let ty' ← zonkValueLevels ty
    return .vNeutral ty' neu
  | .vRecord row =>
    let row' ← zonkValueLevels row
    return .vRecord row'
  | .vVariant row =>
    let row' ← zonkValueLevels row
    return .vVariant row'
  | .vRowExtend label fieldTy tail =>
    let label' ← zonkValueLevels label
    let fieldTy' ← zonkValueLevels fieldTy
    let tail' ← zonkValueLevels tail
    return .vRowExtend label' fieldTy' tail'
  | .vDataType id params =>
    let params' ← params.mapM zonkValueLevels
    return .vDataType id params'
  | .vConstructor name tag args =>
    let args' ← args.mapM zonkValueLevels
    return .vConstructor name tag args'
  | .vEq tyLevel ty lhs rhs =>
    let tyLevel' ← solveLevelVars tyLevel
    let ty' ← zonkValueLevels ty
    let lhs' ← zonkValueLevels lhs
    let rhs' ← zonkValueLevels rhs
    return .vEq tyLevel' ty' lhs' rhs'
  | .vRefl ty x =>
    let ty' ← zonkValueLevels ty
    let x' ← zonkValueLevels x
    return .vRefl ty' x'
  | .vTransport tyLevel ty motive lhs rhs eq body =>
    let tyLevel' ← solveLevelVars tyLevel
    let ty' ← zonkValueLevels ty
    let motive' ← zonkValueLevels motive
    let lhs' ← zonkValueLevels lhs
    let rhs' ← zonkValueLevels rhs
    let eq' ← zonkValueLevels eq
    let body' ← zonkValueLevels body
    return .vTransport tyLevel' ty' motive' lhs' rhs' eq' body'
  -- Values without levels
  | .vPrimTy _ | .vIntLit _ | .vStringLit _
  | .vRowEmpty | .vLabelLit _ | .vRecordVal _
  | .vRowSort | .vLabelSort =>
    return v

/-- Create a fresh Type with a fresh level variable -/
def freshType (name : String := "u") : TCM Value := do
  let l ← TCM.freshLevel name
  return .vType l

/-- Assert that a value is a Type and return its level -/
def assertType (v : Value) : TCM Level := do
  let v' ← force v
  match v' with
  | .vType l => return l
  | .vNeutral (.vType l) _ => return l
  | _ =>
    let span ← TCM.getSpan
    TCM.throw (.expectedType v' span none)

/-- Create the type of a Pi type given domain and codomain levels -/
def piTypeLevel (domLevel codLevel : Level) : Level :=
  Level.mkMax domLevel codLevel

/-- Create the type of a Sigma type given first and second component levels -/
def sigmaTypeLevel (fstLevel sndLevel : Level) : Level :=
  Level.mkMax fstLevel sndLevel

end Soma.Dependent
