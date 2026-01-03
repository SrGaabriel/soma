import Soma.Core.Value
import Soma.Core.Level
import Soma.Core.Eval
import Soma.Dependent.Prelude
import Soma.Dependent.Monad
import Soma.Dependent.Convert
import Soma.Dependent.Error
import Soma.Dependent.Unify.Core
import Soma.Dependent.Unify.Pruning
import Soma.Dependent.Unify.Row
import Soma.Dependent.Unify.Pattern

open Soma.Syntax (Span)

namespace Soma.Dependent

open Soma.Core

mutual

/-- Unify two values. May solve metavariables or postpone constraints -/
partial def unify (v1 v2 : Value) : TCM Unit := do
  -- Force both values first
  let v1' ← force v1
  let v2' ← force v2

  match v1', v2' with
  -- Same constructor: unify recursively
  | .vType l1, .vType l2 =>
    unifyLevel l1 l2

  | .vPi q1 b1 n1 d1 c1, .vPi q2 b2 _ d2 c2 =>
    if q1 != q2 then
      throwUnifyError v1' v2' "quantity mismatch"
    if b1 != b2 then
      throwUnifyError v1' v2' "binder mismatch"
    unify d1 d2
    -- Unify codomains under a fresh variable
    let lvl ← TCM.currentLevel
    let x := Value.vNeutral d1 (.nVar ⟨n1, lvl⟩)
    let cod1 ← applyClosure c1 x
    let cod2 ← applyClosure c2 x
    TCM.withBinding n1 d1 q1 b1 defaultSpan do
      unify cod1 cod2

  | .vLam q1 b1 n1 d1 body1, .vLam q2 b2 _ d2 body2 =>
    if q1 != q2 then
      throwUnifyError v1' v2' "quantity mismatch"
    if b1 != b2 then
      throwUnifyError v1' v2' "binder mismatch"
    unify d1 d2
    let lvl ← TCM.currentLevel
    let x := Value.vNeutral d1 (.nVar ⟨n1, lvl⟩)
    let b1Val ← applyClosure body1 x
    let b2Val ← applyClosure body2 x
    TCM.withBinding n1 d1 q1 b1 defaultSpan do
      unify b1Val b2Val

  | .vSigma q1 n1 f1 s1, .vSigma q2 _ f2 s2 =>
    if q1 != q2 then
      throwUnifyError v1' v2' "quantity mismatch"
    unify f1 f2
    let lvl ← TCM.currentLevel
    let x := Value.vNeutral f1 (.nVar ⟨n1, lvl⟩)
    let snd1 ← applyClosure s1 x
    let snd2 ← applyClosure s2 x
    TCM.withBinding n1 f1 q1 .explicit defaultSpan do
      unify snd1 snd2

  | .vPair a1 b1, .vPair a2 b2 =>
    unify a1 a2
    unify b1 b2

  | .vPrimTy p1, .vPrimTy p2 =>
    if p1 != p2 then throwUnifyError v1' v2' "primitive type mismatch"

  | .vHigherPrim p1, .vHigherPrim p2 =>
    if p1 != p2 then throwUnifyError v1' v2' "higher primitive mismatch"

  | .vIntLit n1, .vIntLit n2 =>
    if n1 != n2 then throwUnifyError v1' v2' "integer mismatch"

  | .vStringLit s1, .vStringLit s2 =>
    if s1 != s2 then throwUnifyError v1' v2' "string mismatch"

  | .vLabelLit l1, .vLabelLit l2 =>
    if l1 != l2 then throwUnifyError v1' v2' "label mismatch"

  | .vRowEmpty, .vRowEmpty => pure ()

  | .vRowExtend l1 t1 r1, .vRowExtend l2 t2 r2 =>
    unifyRows l1 t1 r1 l2 t2 r2

  | .vRecord r1, .vRecord r2 => unify r1 r2

  | .vVariant r1, .vVariant r2 => unify r1 r2

  | .vRecordVal fs1, .vRecordVal fs2 =>
    unifyRecordFields fs1 fs2

  | .vDataType id1 ps1, .vDataType id2 ps2 =>
    if id1 != id2 then
      throwUnifyError v1' v2' "data type mismatch"
    unifyList ps1 ps2

  | .vConstructor n1 t1 as1, .vConstructor n2 t2 as2 =>
    if n1 != n2 || t1 != t2 then throwUnifyError v1' v2' "constructor mismatch"
    unifyList as1 as2

  | .vEq l1 t1 a1 b1, .vEq l2 t2 a2 b2 =>
    unifyLevel l1 l2
    unify t1 t2
    unify a1 a2
    unify b1 b2

  | .vRefl t1 x1, .vRefl t2 x2 =>
    unify t1 t2
    unify x1 x2

  | .vTransport l1 t1 m1 lhs1 rhs1 eq1 b1, .vTransport l2 t2 m2 lhs2 rhs2 eq2 b2 =>
    unifyLevel l1 l2
    unify t1 t2
    unify m1 m2
    unify lhs1 lhs2
    unify rhs1 rhs2
    unify eq1 eq2
    unify b1 b2

  -- Metavariable on the left
  | .vNeutral _ (.nMeta m), rhs =>
    solveMeta m [] rhs

  -- Metavariable on the right
  | lhs, .vNeutral _ (.nMeta m) =>
    solveMeta m [] lhs

  -- Metavariable with spine on the left
  | .vNeutral _ neu1, rhs =>
    match getMetaWithSpine neu1 with
    | some (m, spine) => solveMeta m spine rhs
    | none =>
      match rhs with
      | .vNeutral _ neu2 => unifyNeutral neu1 neu2
      | _ => throwUnifyError v1' v2' "flex-rigid mismatch"

  -- Metavariable with spine on the right
  | lhs, .vNeutral ty2 neu2 =>
    match getMetaWithSpine neu2 with
    | some (m, spine) => solveMeta m spine lhs
    | none =>
      match lhs with
      | .vNeutral _ neu1 => unifyNeutral neu1 neu2
      | _ => throwUnifyError v1' v2' "rigid-flex mismatch"

  -- Eta for functions: v1 = v2 if λx. v1 x = λx. v2 x
  | .vLam _ _ n d body, other =>
    let lvl ← TCM.currentLevel
    let x := Value.vNeutral d (.nVar ⟨n, lvl⟩)
    let bodyVal ← applyClosure body x
    let otherApp := Value.vNeutral d (.nApp (valueToNeutral other) x)
    TCM.withBinding n d .omega .explicit defaultSpan do
      unify bodyVal otherApp

  | other, .vLam _ _ n d body =>
    let lvl ← TCM.currentLevel
    let x := Value.vNeutral d (.nVar ⟨n, lvl⟩)
    let bodyVal ← applyClosure body x
    let otherApp := Value.vNeutral d (.nApp (valueToNeutral other) x)
    TCM.withBinding n d .omega .explicit defaultSpan do
      unify otherApp bodyVal

  -- Eta for pairs: v1 = v2 if (v1.1, v1.2) = (v2.1, v2.2)
  | .vPair a1 b1, other =>
    let (a2, b2) := etaExpandPairValue other
    unify a1 a2
    unify b1 b2

  | other, .vPair a2 b2 =>
    let (a1, b1) := etaExpandPairValue other
    unify a1 a2
    unify b1 b2

  | _, _ =>
    throwUnifyError v1' v2' "incompatible types"

/-- Unify two neutral terms -/
partial def unifyNeutral (n1 n2 : Neutral) : TCM Unit := do
  match n1, n2 with
  | .nVar v1, .nVar v2 =>
    if v1.level != v2.level then
      let span ← TCM.getSpan
      TCM.throw (.unificationFailed (.rigidMismatch n1 n2) .general span)

  | .nMeta m1, .nMeta m2 =>
    if m1 != m2 then
      -- Two different metas: try to solve one with the other
      solveMeta m1 [] (.vNeutral .type0 (.nMeta m2))

  -- Metavariable on left, rigid variable on right: solve meta with the variable
  | .nMeta m, .nVar v =>
    solveMeta m [] (.vNeutral .type0 (.nVar v))

  -- Rigid variable on left, metavariable on right: solve meta with the variable
  | .nVar v, .nMeta m =>
    solveMeta m [] (.vNeutral .type0 (.nVar v))

  | .nApp f1 a1, .nApp f2 a2 =>
    unifyNeutral f1 f2
    unify a1 a2

  | .nFst p1, .nFst p2 =>
    unifyNeutral p1 p2

  | .nSnd p1, .nSnd p2 =>
    unifyNeutral p1 p2

  | .nFieldAccess r1 f1, .nFieldAccess r2 f2 =>
    if f1 != f2 then
      let span ← TCM.getSpan
      TCM.throw (.unificationFailed (.rigidMismatch n1 n2) .general span)
    unifyNeutral r1 r2

  | _, _ =>
    let span ← TCM.getSpan
    TCM.throw (.unificationFailed (.rigidMismatch n1 n2) .general span)

/-- Unify row types with rewriting -/
partial def unifyRows (l1 : Value) (t1 : Value) (r1 : Value)
    (l2 : Value) (t2 : Value) (r2 : Value) : TCM Unit := do
  match l1, l2 with
  | .vLabelLit name1, .vLabelLit name2 =>
    if name1 == name2 then
      -- Same label: unify types and tails
      unify t1 t2
      unify r1 r2
    else
      -- Different labels: try rewriting in both directions
      -- First try to find name1 in row2
      match ← splitRowAt name1 (.vRowExtend l2 t2 r2) with
      | some (foundTy, restRow) =>
        unify t1 foundTy
        unify r1 restRow
      | none =>
        -- Try the other direction: find name2 in row1
        match ← splitRowAt name2 (.vRowExtend l1 t1 r1) with
        | some (foundTy, restRow) =>
          unify t2 foundTy
          unify r2 restRow
        | none =>
          throwUnifyError (.vRowExtend l1 t1 r1) (.vRowExtend l2 t2 r2)
            s!"labels '{name1}' and '{name2}' not found in opposite rows"

  -- Label polymorphism: metavariable label
  | .vNeutral _ (.nMeta m), .vLabelLit _ =>
    solveMeta m [] l2
    unify t1 t2
    unify r1 r2

  | .vLabelLit _, .vNeutral _ (.nMeta m) =>
    solveMeta m [] l1
    unify t1 t2
    unify r1 r2

  | .vNeutral _ (.nMeta m1), .vNeutral _ (.nMeta m2) =>
    -- Both labels are metavariables
    if m1 == m2 then
      unify t1 t2
      unify r1 r2
    else
      -- Postpone this constraint
      let span ← TCM.getSpan
      TCM.postpone (.unify (.vRowExtend l1 t1 r1) (.vRowExtend l2 t2 r2) span)

  | _, _ =>
    -- Try to unify labels directly
    unify l1 l2
    unify t1 t2
    unify r1 r2

/-- Unify record fields (order-independent) -/
partial def unifyRecordFields (fs1 fs2 : List (String × Value)) : TCM Unit := do
  if fs1.length != fs2.length then
    throwUnifyError (.vRecordVal fs1) (.vRecordVal fs2) "different number of fields"

  for (name, val1) in fs1 do
    match fs2.find? (·.1 == name) with
    | some (_, val2) => unify val1 val2
    | none =>
      throwUnifyError (.vRecordVal fs1) (.vRecordVal fs2) s!"field '{name}' not found"

/-- Unify a list of values pairwise -/
partial def unifyList (vs1 vs2 : List Value) : TCM Unit := do
  if vs1.length != vs2.length then
    let span ← TCM.getSpan
    TCM.throw (.unificationFailed
      (.spineLengthMismatch vs1.length vs2.length) .general span)
  for (v1, v2) in vs1.zip vs2 do
    unify v1 v2

/-- Unify two levels -/
partial def unifyLevel (l1 l2 : Level) : TCM Unit := do
  let l1' := l1.simplify
  let l2' := l2.simplify
  if l1' != l2' then
    -- For now, just postpone level constraints
    TCM.postpone (.levelEq l1' l2')

/-- Try to solve a metavariable application: ?m spine = rhs -/
partial def solveMeta (m : MetaId) (spine : List Value) (rhs : Value) : TCM Unit := do
  -- Check if already solved
  match ← TCM.lookupMeta m with
  | some info =>
    match info.solution with
    | some sol =>
      -- Already solved: apply to spine and unify with rhs
      let applied ← applyToSpine sol spine
      unify applied rhs
    | none =>
      -- Not yet solved: try pattern unification
      solvePattern m spine rhs info.type
  | none =>
    let span ← TCM.getSpan
    TCM.throw (.internalError s!"unknown metavariable {m}" span)

/-- Apply a value to a spine of arguments -/
partial def applyToSpine (v : Value) (spine : List Value) : TCM Value := do
  match spine with
  | [] => return v
  | arg :: rest =>
    let v' ← force v
    match v' with
    | .vLam _ _ _ _ body =>
      let result ← applyClosure body arg
      applyToSpine result rest
    | .vNeutral ty neu =>
      let resultTy ← TCM.freshMetaVal (.vType .zero)
      let applied := Value.vNeutral resultTy (.nApp neu arg)
      applyToSpine applied rest
    | _ =>
      let span ← TCM.getSpan
      TCM.throw (.expectedFunction v' span)

/-- Pattern unification: solve ?m x₁...xₙ = rhs
    1. Standard Miller pattern unification
    2. η-expansion to convert non-patterns to patterns
    3. Pruning to restrict metavariable domains
    4. Heterogeneous constraint handling
    5. Spine intersection for flex-flex unification
    6. Twin variable detection for dependent patterns
    7. Occurs check with pruning recovery -/
partial def solvePattern (m : MetaId) (spine : List Value) (rhs : Value) (metaTy : Value)
    : TCM Unit := do
  -- First, check if the meta's type involves unsolved metas (heterogeneous case)
  let shouldDefer ← shouldDeferMeta m
  if shouldDefer then
    -- Defer: the meta's type needs to be solved first
    let span ← TCM.getSpan
    TCM.postpone (.unify (.vNeutral metaTy (.nMeta m)) rhs span)
    return

  -- Check for reflexivity: ?m spine = ?m spine should always succeed
  let rhs' ← force rhs
  match rhs' with
  | .vNeutral _ (.nMeta m2) =>
    if m == m2 && spine.isEmpty then
      return
  | .vNeutral _ neu2 =>
    match getMetaWithSpine neu2 with
    | some (m2, spine2) =>
      if m == m2 && spine.length == spine2.length then
        -- Same meta: check if spines are identical
        let allEqual ← spine.zip spine2 |>.allM fun (v1, v2) => do
          let v1' ← force v1
          let v2' ← force v2
          return valueEq v1' v2'
        if allEqual then
          return
    | none => pure ()
  | _ => pure ()

  -- Check if spine is a pattern (distinct bound variables)
  match spineIsPattern ⟨spine⟩ with
  | some spineLevels =>
    -- Occurs check: prevent infinite types like ?X = List ?X
    if occursIn m rhs then
      -- NEW: Try occurs check with pruning before failing
      let pruned ← tryOccursCheckPruning m spine rhs
      if pruned then
        -- Pruning was attempted, retry unification
        let span ← TCM.getSpan
        TCM.postpone (.unify (.vNeutral metaTy (.nMeta m)) rhs span)
      else
        let span ← TCM.getSpan
        TCM.throw (.unificationFailed (.occursCheck m rhs) .general span)
    else
      -- Scope check: ensure RHS only references variables in the spine
      if !inScope spineLevels rhs then
        -- Try pruning: can we restrict the meta's domain?
        let _ ← tryPrune m spine rhs

        -- RHS contains variables not in scope - postpone rather than fail
        -- (it might become solvable after more unification)
        let span ← TCM.getSpan
        TCM.postpone (.unify (.vNeutral metaTy (.nMeta m)) rhs span)
      else
        -- Check for twin variables (dependent pattern matching)
        let twins := detectTwinVars spine rhs
        if !twins.isEmpty && allVarsCoveredByTwins twins rhs then
          -- All RHS variables are twins with spine variables
          -- This is solvable via identity-like substitution
          let subst := mkSubst spineLevels
          match applySubst subst rhs with
          | some solutionBody =>
            let solution := buildLambdaSolution spineLevels solutionBody
            let solutionVal ← evalSolutionTerm solution
            TCM.solveMeta m solutionVal
          | none =>
            let span ← TCM.getSpan
            TCM.postpone (.unify (.vNeutral metaTy (.nMeta m)) rhs span)
        else
          -- Build substitution from spine levels
          let subst := mkSubst spineLevels

          -- Apply substitution to RHS to get the solution body
          match applySubst subst rhs with
          | some solutionBody =>
            -- Build the solution as nested lambdas
            let solution := buildLambdaSolution spineLevels solutionBody
            -- Evaluate the solution to a Value
            let solutionVal ← evalSolutionTerm solution
            -- Record the solution
            TCM.solveMeta m solutionVal
          | none =>
            -- RHS contains variables not in the spine - postpone
            let span ← TCM.getSpan
            TCM.postpone (.unify (.vNeutral metaTy (.nMeta m)) rhs span)

  | none =>
    -- Not a pattern - try η-expansion to make it one
    match ← tryMakePatternViaEta m spine rhs with
    | some (extendedSpine, newRhs) =>
      -- η-expansion succeeded! Try solving with the extended spine
      -- This recursive call will now have a proper pattern
      solvePattern m extendedSpine newRhs metaTy
    | none =>
      -- η-expansion didn't help - try flex-flex case
      match rhs with
      | .vNeutral _ (.nMeta m2) =>
        -- Flex-flex: ?m spine = ?m2
        -- Try to solve by intersection if spines overlap
        if m == m2 then
          -- Same meta: always succeeds (reflexivity)
          pure ()
        else
          -- Different metas: try pruning both or postpone
          let _ ← tryPrune m spine rhs
          let span ← TCM.getSpan
          TCM.postpone (.unify (.vNeutral metaTy (.nMeta m)) rhs span)
      | .vNeutral _ neu2 =>
        match getMetaWithSpine neu2 with
        | some (m2, spine2) =>
          -- Flex-flex with spines: ?m spine1 = ?m2 spine2
          if m == m2 then
            -- Same meta with different spines - check if spines are equal
            if spine.length == spine2.length then
              -- Try to unify the spines
              for (v1, v2) in spine.zip spine2 do
                unify v1 v2
            else
              -- Different length spines - postpone
              let span ← TCM.getSpan
              TCM.postpone (.unify (.vNeutral metaTy (.nMeta m)) rhs span)
          else
            -- NEW: Different metas with spines - try spine intersection
            let intersected ← tryFlexFlexIntersection m spine m2 spine2
            if intersected then
              -- Successfully solved via intersection
              pure ()
            else
              -- Intersection failed, postpone
              let span ← TCM.getSpan
              TCM.postpone (.unify (.vNeutral metaTy (.nMeta m)) rhs span)
        | none =>
          -- Not a meta application - postpone
          let span ← TCM.getSpan
          TCM.postpone (.unify (.vNeutral metaTy (.nMeta m)) rhs span)
      | _ =>
        -- Not a pattern and not flex-flex - postpone
        let span ← TCM.getSpan
        TCM.postpone (.unify (.vNeutral metaTy (.nMeta m)) rhs span)

end

/-- Try to solve a single postponed constraint -/
def solveConstraint (c : Constraint) : TCM Bool := do
  match c with
  | .unify v1 v2 span =>
    TCM.withSpan span do
      try
        unify v1 v2
        return true
      catch _ =>
        return false

  | .subtype v1 v2 span =>
    TCM.withSpan span do
      try
        unify v1 v2 -- For now, subtyping is just equality
        return true
      catch _ =>
        return false

  | .levelEq l1 l2 =>
    -- Level constraints need a dedicated solver
    -- For now, just check equality
    if l1.simplify == l2.simplify then
      return true
    else
      return false

  | .levelLe l1 l2 =>
    -- TODO: generate substitutions
    let l1' := l1.simplify
    let l2' := l2.simplify
    match l1', l2' with
    | .lit n1, .lit n2 => return n1 ≤ n2
    | _, _ => return false  -- Can't determine

/-- A min-heap priority queue for constraints, keyed by complexity (unsolved meta count).
    Uses a binary heap stored in an array for O(log n) insert and extractMin. -/
structure ConstraintPQueue where
  /-- Heap array: (priority, constraint) pairs, min-heap ordered by priority -/
  heap : Array (Nat × TrackedConstraint) := #[]
  deriving Inhabited

namespace ConstraintPQueue

/-- Create an empty priority queue -/
def empty : ConstraintPQueue := ⟨#[]⟩

/-- Check if queue is empty -/
def isEmpty (pq : ConstraintPQueue) : Bool := pq.heap.isEmpty

/-- Number of elements in queue -/
def size (pq : ConstraintPQueue) : Nat := pq.heap.size

/-- Swap elements at two indices -/
private def swap (arr : Array (Nat × TrackedConstraint)) (i j : Nat) : Array (Nat × TrackedConstraint) :=
  if i < arr.size && j < arr.size then
    let vi := arr[i]!
    let vj := arr[j]!
    let arr' := arr.set! i vj
    arr'.set! j vi
  else arr

/-- Bubble up element at index to maintain heap property -/
private partial def bubbleUp (arr : Array (Nat × TrackedConstraint)) (idx : Nat) : Array (Nat × TrackedConstraint) :=
  if idx == 0 then arr
  else
    let parentIdx := (idx - 1) / 2
    if idx < arr.size && parentIdx < arr.size then
      let (prio, _) := arr[idx]!
      let (parentPrio, _) := arr[parentIdx]!
      if prio < parentPrio then
        bubbleUp (swap arr idx parentIdx) parentIdx
      else arr
    else arr

/-- Bubble down element at index to maintain heap property -/
private partial def bubbleDown (arr : Array (Nat × TrackedConstraint)) (idx : Nat) : Array (Nat × TrackedConstraint) :=
  let leftIdx := 2 * idx + 1
  let rightIdx := 2 * idx + 2
  let sz := arr.size

  if leftIdx >= sz then arr  -- No children
  else
    -- Find smallest child
    let smallestIdx :=
      if rightIdx < sz then
        let (leftPrio, _) := arr[leftIdx]!
        let (rightPrio, _) := arr[rightIdx]!
        if leftPrio <= rightPrio then leftIdx else rightIdx
      else leftIdx

    if idx < sz && smallestIdx < sz then
      let (prio, _) := arr[idx]!
      let (smallestPrio, _) := arr[smallestIdx]!
      if smallestPrio < prio then
        bubbleDown (swap arr idx smallestIdx) smallestIdx
      else arr
    else arr

/-- Insert a constraint with given priority -/
def insert (pq : ConstraintPQueue) (priority : Nat) (tc : TrackedConstraint) : ConstraintPQueue :=
  let newHeap := pq.heap.push (priority, tc)
  ⟨bubbleUp newHeap (newHeap.size - 1)⟩

/-- Extract minimum priority element, returns (element, new queue) or none if empty -/
def extractMin (pq : ConstraintPQueue) : Option (TrackedConstraint × ConstraintPQueue) :=
  if h : pq.heap.size > 0 then
    let tc := (pq.heap[0]'h).2
    if pq.heap.size == 1 then
      some (tc, ⟨#[]⟩)
    else
      -- Move last element to root and bubble down
      let lastElem := pq.heap.back!
      let newHeap := (pq.heap.set! 0 lastElem).pop
      some (tc, ⟨bubbleDown newHeap 0⟩)
  else none

/-- Build a priority queue from an array of (priority, constraint) pairs -/
def fromArray (arr : Array (Nat × TrackedConstraint)) : ConstraintPQueue :=
  arr.foldl (fun pq (prio, tc) => pq.insert prio tc) empty

end ConstraintPQueue

/-- Count how many unsolved metas are in a constraint -/
def countUnsolvedMetas (metas : Array MetaId) : TCM Nat := do
  let mut count := 0
  for mid in metas do
    let solved ← TCM.isMetaSolved mid
    if !solved then
      count := count + 1
  return count

/-- Build a priority queue from constraints, prioritized by complexity (fewer unsolved metas = higher priority) -/
def buildConstraintQueue (constraints : Array TrackedConstraint) : TCM ConstraintPQueue := do
  let mut pq := ConstraintPQueue.empty
  for tc in constraints do
    let complexity ← countUnsolvedMetas tc.metas
    pq := pq.insert complexity tc
  return pq

/-- Sort constraints by complexity (fewer unsolved metas first) - kept for compatibility -/
def sortByComplexity (constraints : Array TrackedConstraint) : TCM (Array TrackedConstraint) := do
  -- Compute complexity for each constraint
  let mut withComplexity : Array (TrackedConstraint × Nat) := #[]
  for tc in constraints do
    let complexity ← countUnsolvedMetas tc.metas
    withComplexity := withComplexity.push (tc, complexity)
  -- Sort by complexity (simpler first)
  let sorted := withComplexity.qsort (fun (_, c1) (_, c2) => c1 < c2)
  return sorted.map (·.1)

/-- Run the constraint solver using priority queue for efficient ordering.
    Returns the remaining unsolved constraints. -/
def solveConstraints : TCM (Array Constraint) := do
  let allConstraints ← TCM.getPostponedTracked
  TCM.clearPostponed

  -- Build initial priority queue
  let mut pq ← buildConstraintQueue allConstraints
  let mut unsolved : Array TrackedConstraint := #[]
  let mut progress := true
  let mut iterations := 0
  let maxIterations := maxConstraintIterations

  -- Keep trying while we make progress
  while progress && iterations < maxIterations do
    progress := false
    iterations := iterations + 1

    -- Process constraints from priority queue (lowest complexity first)
    let mut nextRoundQueue := ConstraintPQueue.empty

    while !pq.isEmpty do
      match pq.extractMin with
      | none => break
      | some (tc, pq') =>
        pq := pq'

        -- Check if any metas in this constraint are now solved
        let hasSolvedMeta ← tc.metas.anyM TCM.isMetaSolved

        -- Try to solve if we have newly solved metas or on first iteration
        let shouldTry := hasSolvedMeta || iterations == 1

        if shouldTry then
          if ← solveConstraint tc.constraint then
            progress := true
            -- When a constraint is solved, wake up constraints that depend on its metas
            for mid in tc.metas do
              let isSolved ← TCM.isMetaSolved mid
              if isSolved then
                TCM.wakeConstraintsFor mid
          else
            -- Constraint still unsolved, re-add with updated priority
            let newPostponed ← TCM.getPostponedTracked
            TCM.clearPostponed
            for newTc in newPostponed do
              let complexity ← countUnsolvedMetas newTc.metas
              nextRoundQueue := nextRoundQueue.insert complexity newTc
            -- Re-compute priority for unsolved constraint
            let complexity ← countUnsolvedMetas tc.metas
            unsolved := unsolved.push tc
        else
          -- Skip this constraint for now, preserve priority
          let complexity ← countUnsolvedMetas tc.metas
          nextRoundQueue := nextRoundQueue.insert complexity tc

    -- Prepare for next iteration
    if progress then
      -- Re-add unsolved to queue with updated priorities
      for tc in unsolved do
        let complexity ← countUnsolvedMetas tc.metas
        nextRoundQueue := nextRoundQueue.insert complexity tc
      pq := nextRoundQueue
      unsolved := #[]
    else
      pq := nextRoundQueue

  -- Collect remaining unsolved from queue
  while !pq.isEmpty do
    match pq.extractMin with
    | none => break
    | some (tc, pq') =>
      pq := pq'
      unsolved := unsolved.push tc

  return unsolved.map (·.constraint)

/-- Solve constraints with worklist-driven approach (more efficient for large constraint sets) -/
def solveConstraintsWorklist : TCM (Array Constraint) := do
  -- Initialize: add all constraints to worklist
  let allConstraints ← TCM.getPostponedTracked
  TCM.clearPostponed

  -- Track which constraints are still active
  let mut activeConstraints : Std.HashMap Nat TrackedConstraint := {}
  for tc in allConstraints do
    activeConstraints := activeConstraints.insert tc.constraintId.id tc

  -- Initialize worklist with all constraint IDs, sorted by complexity
  let sorted ← sortByComplexity allConstraints
  let mut worklist : Array ConstraintId := sorted.map (·.constraintId)

  let mut iterations := 0
  let maxIterations := maxConstraintIterations * 10  -- Higher limit for worklist approach

  while !worklist.isEmpty && iterations < maxIterations do
    iterations := iterations + 1

    -- Pop from worklist
    let cid := worklist[0]!
    worklist := worklist.extract 1 worklist.size

    -- Skip if already solved/removed
    match activeConstraints.get? cid.id with
    | none => continue
    | some tc =>
      if ← solveConstraint tc.constraint then
        -- Solved! Remove from active set
        activeConstraints := activeConstraints.erase cid.id

        -- Wake up constraints that share metas with this one
        for mid in tc.metas do
          let isSolved ← TCM.isMetaSolved mid
          if isSolved then
            -- Find all constraints that reference this meta
            let state ← TCM.getState
            let affectedCids := state.metas.getAffectedConstraints mid
            for affectedCid in affectedCids do
              -- Only add if still active and not already in worklist
              if activeConstraints.contains affectedCid.id then
                if !worklist.contains affectedCid then
                  worklist := worklist.push affectedCid
      else
        -- Still unsolved, might get new constraints
        let newPostponed ← TCM.getPostponedTracked
        TCM.clearPostponed
        for newTc in newPostponed do
          activeConstraints := activeConstraints.insert newTc.constraintId.id newTc
          worklist := worklist.push newTc.constraintId

  -- Return remaining unsolved constraints
  return activeConstraints.toList.map (·.2.constraint) |>.toArray

end Soma.Dependent
