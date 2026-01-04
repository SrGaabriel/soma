/-
  Unified Constraint Graph Solver

  This module provides a unified constraint solving infrastructure that combines
  the best aspects of the priority queue and worklist approaches:

  1. **Priority-based scheduling**: Constraints with fewer unsolved metas are tried first
  2. **Dependency-driven wake-up**: When a meta is solved, dependent constraints are re-queued
  3. **Efficient data structures**: HashMap for O(1) constraint lookup, priority queue for scheduling
  4. **Bounded iteration**: Fuel-based limits to prevent infinite loops
  5. **Error recovery**: Collect errors but continue solving other constraints
  6. **Constraint provenance**: Track origin and parent constraints for better error messages

  ## Architecture

  The `ConstraintGraph` maintains:
  - All active constraints indexed by ID
  - Meta → constraint dependency mapping
  - Priority queue for scheduling (by complexity)
  - Blocked constraints waiting on specific metas
  - Constraint provenance for error chain reconstruction

  ## Algorithm

  1. Initialize graph with all postponed constraints
  2. While queue is non-empty and fuel remains:
     a. Pop lowest-complexity constraint
     b. Try to solve it
     c. If solved: remove and wake dependents
     d. If blocked: move to blocked set
     e. If failed: compute minimal unsatisfiable set, record error with chain, and remove
  3. Return remaining unsolved constraints
-/

import Soma.Core.Value
import Soma.Core.Level
import Soma.Dependent.Monad
import Soma.Dependent.Error
import Std.Data.HashMap
import Std.Data.HashSet

namespace Soma.Dependent.Unify

open Soma.Core (Value MetaId ConstraintId)
open Soma.Syntax (Span)
open Std (HashMap HashSet)

/-- Result of attempting to solve a constraint -/
inductive SolveResult where
  /-- Constraint was solved successfully -/
  | solved
  /-- Constraint is blocked on unsolved metas -/
  | blocked (metas : Array MetaId)
  /-- Constraint could not be solved (but may succeed later with more info) -/
  | deferred
  /-- Constraint failed with an error -/
  | failed (error : TCError)
  deriving Inhabited

/-- Unified constraint graph for efficient constraint solving -/
structure ConstraintGraph where
  /-- All active constraints indexed by ID -/
  constraints : HashMap Nat TrackedConstraint := {}
  /-- Meta → constraints that reference it -/
  metaToConstraints : HashMap Nat (HashSet Nat) := {}
  /-- Priority queue: (complexity, constraintId) pairs, min-heap by complexity -/
  queue : Array (Nat × Nat) := #[]
  /-- Constraints blocked on specific metas -/
  blocked : HashMap Nat (Array Nat) := {}
  /-- Next constraint ID for newly created constraints -/
  nextId : Nat := 0
  deriving Inhabited

namespace ConstraintGraph

/-- Create an empty constraint graph -/
def empty : ConstraintGraph := {}

/-- Check if the graph has no pending constraints -/
def isEmpty (g : ConstraintGraph) : Bool :=
  g.queue.isEmpty && g.blocked.isEmpty

/-- Number of active constraints -/
def size (g : ConstraintGraph) : Nat :=
  g.constraints.size

/-- Bubble up element at index in heap -/
private partial def bubbleUp (arr : Array (Nat × Nat)) (idx : Nat) : Array (Nat × Nat) :=
  if idx == 0 then arr
  else
    let parentIdx := (idx - 1) / 2
    if idx < arr.size && parentIdx < arr.size then
      let (prio, _) := arr[idx]!
      let (parentPrio, _) := arr[parentIdx]!
      if prio < parentPrio then
        let vi := arr[idx]!
        let vp := arr[parentIdx]!
        bubbleUp (arr.set! idx vp |>.set! parentIdx vi) parentIdx
      else arr
    else arr

/-- Bubble down element at index in heap -/
private partial def bubbleDown (arr : Array (Nat × Nat)) (idx : Nat) : Array (Nat × Nat) :=
  let leftIdx := 2 * idx + 1
  let rightIdx := 2 * idx + 2
  let sz := arr.size

  if leftIdx >= sz then arr
  else
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
        let vi := arr[idx]!
        let vs := arr[smallestIdx]!
        bubbleDown (arr.set! idx vs |>.set! smallestIdx vi) smallestIdx
      else arr
    else arr

/-- Insert a constraint into the graph -/
def insert (g : ConstraintGraph) (tc : TrackedConstraint) (complexity : Nat) : ConstraintGraph :=
  let cid := tc.constraintId.id
  -- Add to constraints map
  let constraints' := g.constraints.insert cid tc
  -- Add to meta -> constraint mapping
  let metaToConstraints' := tc.metas.foldl (init := g.metaToConstraints) fun acc mid =>
    let existing := acc.getD mid.id {}
    acc.insert mid.id (existing.insert cid)
  -- Add to priority queue
  let queue' := bubbleUp (g.queue.push (complexity, cid)) g.queue.size
  { g with
    constraints := constraints'
    metaToConstraints := metaToConstraints'
    queue := queue' }

/-- Extract the minimum complexity constraint from the queue (non-recursive version) -/
def extractMin (g : ConstraintGraph) : Option (TrackedConstraint × ConstraintGraph) := Id.run do
  let mut g' := g
  while h : g'.queue.size > 0 do
    let (_, cid) := g'.queue[0]'h
    let queue' := if g'.queue.size == 1 then #[]
      else bubbleDown (g'.queue.set! 0 g'.queue.back! |>.pop) 0
    g' := { g' with queue := queue' }
    match g.constraints.get? cid with
    | none =>
      -- Constraint was removed, continue to next
      continue
    | some tc =>
      return some (tc, g')
  return none

/-- Remove a constraint from the graph -/
def remove (g : ConstraintGraph) (cid : Nat) : ConstraintGraph :=
  match g.constraints.get? cid with
  | none => g
  | some tc =>
    -- Remove from constraints map
    let constraints' := g.constraints.erase cid
    -- Remove from meta -> constraint mapping
    let metaToConstraints' := tc.metas.foldl (init := g.metaToConstraints) fun acc mid =>
      match acc.get? mid.id with
      | none => acc
      | some set => acc.insert mid.id (set.erase cid)
    -- Remove from blocked if present
    let blocked' := tc.metas.foldl (init := g.blocked) fun acc mid =>
      match acc.get? mid.id with
      | none => acc
      | some arr => acc.insert mid.id (arr.filter (· != cid))
    { g with
      constraints := constraints'
      metaToConstraints := metaToConstraints'
      blocked := blocked' }

/-- Mark a constraint as blocked on a specific meta -/
def blockOn (g : ConstraintGraph) (cid : Nat) (mid : MetaId) : ConstraintGraph :=
  let existing := g.blocked.getD mid.id #[]
  if existing.contains cid then g
  else { g with blocked := g.blocked.insert mid.id (existing.push cid) }

/-- Count unsolved metas in a constraint -/
def countUnsolvedMetas (metas : Array MetaId) : TCM Nat := do
  let mut count := 0
  for mid in metas do
    let solved ← TCM.isMetaSolved mid
    if !solved then
      count := count + 1
  return count

/-- Wake up constraints blocked on a meta (re-add to queue) -/
def wakeBlocked (g : ConstraintGraph) (mid : MetaId) : TCM ConstraintGraph := do
  let blockedCids := g.blocked.getD mid.id #[]
  let mut g' := { g with blocked := g.blocked.erase mid.id }
  for cid in blockedCids do
    match g'.constraints.get? cid with
    | none => pure ()
    | some tc =>
      -- Re-compute complexity and add back to queue
      let complexity ← countUnsolvedMetas tc.metas
      g' := { g' with queue := bubbleUp (g'.queue.push (complexity, cid)) g'.queue.size }
  return g'

/-- Get all constraints that reference a meta -/
def getConstraintsFor (g : ConstraintGraph) (mid : MetaId) : Array TrackedConstraint :=
  let cids := g.metaToConstraints.getD mid.id {}
  cids.fold (init := #[]) fun acc cid =>
    match g.constraints.get? cid with
    | none => acc
    | some tc => acc.push tc

/-- Get the constraint chain (ancestors) for a constraint.
    Uses fuel to ensure termination. -/
def getConstraintChain (g : ConstraintGraph) (tc : TrackedConstraint) : Array ConstraintInfo :=
  -- Start with current constraint's info
  let chain0 := #[tc.toInfo]
  -- BFS through parent constraints with fuel = max constraints
  let fuel := g.constraints.size + 1
  go fuel chain0 {} tc.parentConstraints.toList
where
  go (fuel : Nat) (chain : Array ConstraintInfo) (visited : HashSet Nat)
      (queue : List ConstraintId) : Array ConstraintInfo :=
    match fuel with
    | 0 => chain  -- Out of fuel, return what we have
    | fuel' + 1 =>
      match queue with
      | [] => chain
      | current :: rest =>
        if visited.contains current.id then
          go fuel' chain visited rest
        else
          let visited' := visited.insert current.id
          match g.constraints.get? current.id with
          | some parentTc =>
            let chain' := chain.push parentTc.toInfo
            let newParents := parentTc.parentConstraints.toList.filter
              fun gp => !visited'.contains gp.id
            go fuel' chain' visited' (rest ++ newParents)
          | none =>
            go fuel' chain visited' rest

/-- Compute the minimal unsatisfiable constraint set for a failed constraint.
    This walks the dependency graph to find which constraints contributed to the failure. -/
def computeMinimalUnsatisfiableSet (g : ConstraintGraph) (failedTc : TrackedConstraint)
    : TCM (Array ConstraintInfo × Array MetaId) := do
  let mut relevantConstraints : Array ConstraintInfo := #[]
  let mut relevantMetas : Array MetaId := #[]
  let mut visited : HashSet Nat := {}

  -- Start with the failed constraint
  relevantConstraints := relevantConstraints.push failedTc.toInfo

  -- Add all parent constraints
  let mut queue := failedTc.parentConstraints
  while h : queue.size > 0 do
    let cid := queue[0]'h
    queue := queue.extract 1 queue.size

    if visited.contains cid.id then
      continue
    visited := visited.insert cid.id

    match g.constraints.get? cid.id with
    | some tc =>
      relevantConstraints := relevantConstraints.push tc.toInfo
      for parent in tc.parentConstraints do
        if !visited.contains parent.id then
          queue := queue.push parent
    | none => pure ()

  -- Collect all metas involved in the failed constraint and its ancestors
  for mid in failedTc.metas do
    if !relevantMetas.contains mid then
      relevantMetas := relevantMetas.push mid

  -- Also collect metas from related constraints (those sharing metas with the failed one)
  for mid in failedTc.metas do
    for relatedTc in g.getConstraintsFor mid do
      if !visited.contains relatedTc.constraintId.id then
        -- Only include if it's directly related (shares a meta)
        for m in relatedTc.metas do
          if failedTc.metas.contains m && !relevantMetas.contains m then
            relevantMetas := relevantMetas.push m

  return (relevantConstraints, relevantMetas)

/-- Build a constraint graph from postponed constraints -/
def fromPostponed : TCM ConstraintGraph := do
  let allConstraints ← TCM.getPostponedTracked
  TCM.clearPostponed
  let mut g := ConstraintGraph.empty
  for tc in allConstraints do
    let complexity ← countUnsolvedMetas tc.metas
    g := g.insert tc complexity
  return g

end ConstraintGraph

/-- Default fuel for constraint solving -/
def constraintSolverFuel : Nat := 10000

/-- Enhance an error with constraint chain information -/
def enhanceErrorWithChain (error : TCError) (chain : Array ConstraintInfo)
    (metas : Array MetaId) : TCError :=
  match error with
  | .unificationFailed failure purpose span _ _ =>
    .unificationFailed failure purpose span chain metas
  | .typeMismatch expected actual purpose expectedSpan actualSpan _ =>
    .typeMismatch expected actual purpose expectedSpan actualSpan chain
  | other => other

/-- Main unified constraint solver using the constraint graph -/
def solveConstraintGraph (tryConstraint : Constraint → TCM SolveResult)
    (fuel : Nat := constraintSolverFuel) : TCM (Array Constraint) := do
  let mut g ← ConstraintGraph.fromPostponed
  let mut remainingFuel := fuel
  let mut solvedCount := 0

  -- Main solving loop
  while remainingFuel > 0 do
    remainingFuel := remainingFuel - 1

    -- Try to extract a constraint from the queue
    match g.extractMin with
    | none =>
      -- Queue is empty, check if there are blocked constraints
      if g.blocked.isEmpty then
        break  -- All done!
      else
        -- Still have blocked constraints but nothing in queue
        -- This means we're stuck - these constraints may need more info
        break
    | some (tc, g') =>
      g := g'

      -- Try to solve this constraint
      let result ← tryConstraint tc.constraint

      match result with
      | .solved =>
        -- Successfully solved! Remove from graph
        g := g.remove tc.constraintId.id
        solvedCount := solvedCount + 1

        -- Wake up constraints that depend on metas we may have solved
        for mid in tc.metas do
          let isSolved ← TCM.isMetaSolved mid
          if isSolved then
            g ← g.wakeBlocked mid
            -- Also re-queue any constraints from metaToConstraints
            for depTc in g.getConstraintsFor mid do
              let complexity ← ConstraintGraph.countUnsolvedMetas depTc.metas
              g := { g with queue := ConstraintGraph.bubbleUp (g.queue.push (complexity, depTc.constraintId.id)) g.queue.size }

      | .blocked metas =>
        -- Constraint is blocked, move to blocked set
        for mid in metas do
          g := g.blockOn tc.constraintId.id mid

      | .deferred =>
        -- Constraint couldn't make progress, re-add with same complexity
        let complexity ← ConstraintGraph.countUnsolvedMetas tc.metas
        g := { g with queue := ConstraintGraph.bubbleUp (g.queue.push (complexity, tc.constraintId.id)) g.queue.size }

      | .failed error =>
        -- Constraint failed - compute minimal unsatisfiable set and record enhanced error
        let (chain, metas) ← g.computeMinimalUnsatisfiableSet tc
        let enhancedError := enhanceErrorWithChain error chain metas
        TCM.addError enhancedError
        g := g.remove tc.constraintId.id

    -- Check for newly postponed constraints and add them
    let newPostponed ← TCM.getPostponedTracked
    if !newPostponed.isEmpty then
      TCM.clearPostponed
      for tc in newPostponed do
        let complexity ← ConstraintGraph.countUnsolvedMetas tc.metas
        g := g.insert tc complexity

  -- Collect remaining unsolved constraints
  let mut unsolved : Array Constraint := #[]
  for (_, tc) in g.constraints do
    unsolved := unsolved.push tc.constraint

  return unsolved

end Soma.Dependent.Unify
