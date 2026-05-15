import Soma.Core.Value
import Soma.Core.Level
import Soma.Dependent.Monad
import Soma.Dependent.Error
import Soma.Dependent.Unify.Core
import Std.Data.HashMap
import Std.Data.HashSet

namespace Soma.Dependent.Unify

open Soma.Core (Value MetaId LevelVarId ConstraintId)
open Soma.Syntax (Span)
open Std (HashMap HashSet)

/-- A cluster of related constraints -/
structure ConstraintCluster where
  /-- Constraint IDs in this cluster -/
  constraintIds : Array Nat
  /-- All metas referenced by constraints in this cluster -/
  metas : HashSet Nat
  /-- Priority: lower is higher priority (based on min complexity in cluster) -/
  priority : Nat
  deriving Inhabited

namespace ConstraintCluster



end ConstraintCluster

/-- A solving strategy -/
inductive SolveStrategy where
  /-- Solve by priority (fewest unsolved metas first) -/
  | priority
  /-- Solve by cluster, smallest clusters first -/
  | smallestClusterFirst
  /-- Solve by cluster, largest clusters first (may make more progress) -/
  | largestClusterFirst
  deriving Inhabited, BEq

/-- Result of speculative solving with a particular strategy -/
structure SpeculativeResult where
  /-- Number of constraints solved -/
  solvedCount : Nat
  /-- Number of constraints remaining -/
  remainingCount : Nat
  /-- Errors encountered -/
  errorCount : Nat
  /-- The strategy used -/
  strategy : SolveStrategy
  deriving Inhabited

/-- Result of attempting to solve a constraint -/
inductive SolveResult where
  /-- Constraint was solved successfully -/
  | solved
  /-- Constraint is blocked -/
  | blocked (metas : Array MetaId) (levelVars : Array LevelVarId)
  /-- Constraint couldn't make progress in this pass -/
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
  /-- Constraints blocked waiting for a specific level variable to be solved -/
  blockedOnLevelVar : HashMap Nat (Array Nat) := {}
  /-- Next constraint ID for newly created constraints -/
  nextId : Nat := 0
  /-- Constraint clusters (lazily computed) -/
  clusters : Option (Array ConstraintCluster) := none
  /-- Current solving strategy -/
  strategy : SolveStrategy := .priority
  deriving Inhabited

namespace ConstraintGraph

/-- Create an empty constraint graph -/
def empty : ConstraintGraph := {}



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
    let blockedOnLevelVar' := tc.levelVars.foldl (init := g.blockedOnLevelVar) fun acc lv =>
      match acc.get? lv.id with
      | none => acc
      | some arr => acc.insert lv.id (arr.filter (· != cid))
    { g with
      constraints := constraints'
      metaToConstraints := metaToConstraints'
      blocked := blocked'
      blockedOnLevelVar := blockedOnLevelVar' }

/-- Mark a constraint as blocked on a specific meta -/
def blockOn (g : ConstraintGraph) (cid : Nat) (mid : MetaId) : ConstraintGraph :=
  let existing := g.blocked.getD mid.id #[]
  if existing.contains cid then g
  else { g with blocked := g.blocked.insert mid.id (existing.push cid) }

/-- Mark a constraint as blocked on a specific level variable -/
def blockOnLevelVar (g : ConstraintGraph) (cid : Nat) (lv : LevelVarId)
    : ConstraintGraph :=
  let existing := g.blockedOnLevelVar.getD lv.id #[]
  if existing.contains cid then g
  else { g with blockedOnLevelVar := g.blockedOnLevelVar.insert lv.id (existing.push cid) }

/-- Count unsolved metas in a constraint -/
def countUnsolvedMetas (metas : Array MetaId) : TCM Nat := do
  let mut count := 0
  for mid in metas do
    let solved ← TCM.isMetaSolved mid
    if !solved then
      count := count + 1
  return count


/-- Wake up constraints blocked on a level variable -/
def wakeBlockedOnLevelVar (g : ConstraintGraph) (lv : LevelVarId)
    : TCM ConstraintGraph := do
  let blockedCids := g.blockedOnLevelVar.getD lv.id #[]
  let mut g' := { g with blockedOnLevelVar := g.blockedOnLevelVar.erase lv.id }
  for cid in blockedCids do
    match g'.constraints.get? cid with
    | none => pure ()
    | some tc =>
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

namespace TarjanSCC

/-- DFS state -/
private structure State where
  index : Nat := 0
  indices : HashMap Nat Nat := {}
  lowlinks : HashMap Nat Nat := {}
  onStack : HashSet Nat := {}
  stack : Array Nat := #[]
  sccs : Array (Array Nat) := #[]
  deriving Inhabited

/-- Pop nodes off the stack until we hit `target` -/
private partial def popScc (s : State) (target : Nat) (acc : Array Nat) : State × Array Nat :=
  if h : s.stack.size > 0 then
    let top := s.stack[s.stack.size - 1]'(by
      have : s.stack.size - 1 < s.stack.size := Nat.sub_lt h (by decide)
      exact this)
    let s' : State := { s with
      stack := s.stack.pop
      onStack := s.onStack.erase top }
    let acc' := acc.push top
    if top == target then (s', acc')
    else popScc s' target acc'
  else (s, acc)

/-- Tarjan's `strongconnect` step -/
private partial def visit (graph : HashMap Nat (Array Nat)) (v : Nat) (st : State) : State := Id.run do
  let mut s := st
  let vIdx := s.index
  s := { s with
    indices := s.indices.insert v vIdx
    lowlinks := s.lowlinks.insert v vIdx
    index := vIdx + 1
    stack := s.stack.push v
    onStack := s.onStack.insert v }
  for w in graph.getD v #[] do
    if !s.indices.contains w then
      s := visit graph w s
      let lwv := s.lowlinks.getD v 0
      let lww := s.lowlinks.getD w 0
      if lww < lwv then
        s := { s with lowlinks := s.lowlinks.insert v lww }
    else if s.onStack.contains w then
      let lwv := s.lowlinks.getD v 0
      let idxw := s.indices.getD w 0
      if idxw < lwv then
        s := { s with lowlinks := s.lowlinks.insert v idxw }
  if s.lowlinks.getD v 0 == s.indices.getD v 0 then
    let (s', scc) := popScc s v #[]
    return { s' with sccs := s'.sccs.push scc }
  return s

/-- Run Tarjan's SCC over the given adjacency map -/
def run (graph : HashMap Nat (Array Nat)) (nodes : Array Nat) : Array (Array Nat) := Id.run do
  let mut s : State := {}
  for v in nodes do
    if !s.indices.contains v then
      s := visit graph v s
  return s.sccs

end TarjanSCC

/-- Build the meta-to-meta dependency adjacency map from a `MetaState` -/
def buildMetaDepGraph (metas : Soma.Core.MetaState) : HashMap Nat (Array Nat) :=
  metas.metas.fold (init := {}) fun acc mid info =>
    let typeDeps : Array Nat := info.dependsOn.map (·.id)
    let solDeps : Array Nat :=
      match info.solution with
      | some sol => (Value.collectMetas sol).map (·.id)
      | none => #[]
    let merged := (typeDeps ++ solDeps).toList.eraseDups.filter (· != mid)
    acc.insert mid merged.toArray



/-- Invalidate cached clusters (call when constraints change) -/
def invalidateClusters (g : ConstraintGraph) : ConstraintGraph :=
  { g with clusters := none }


/-- Get only the constraints related to a solved meta (for smart retrying).
    This returns constraints that:
    1. Directly reference the meta
    2. Reference metas that depend on the solved meta
    Instead of returning all constraints, we only return related ones. -/
def getRelatedConstraints (g : ConstraintGraph) (mid : MetaId) : Array Nat :=
  -- Get direct constraints
  let directCids := g.metaToConstraints.getD mid.id {}

  -- Also get constraints in the same cluster
  match g.clusters with
  | none =>
    -- No clusters computed, just return direct constraints
    directCids.fold (init := #[]) fun acc cid => acc.push cid
  | some clusters =>
    -- Find the cluster containing this meta and return all its constraints
    let clusterResult := clusters.foldl (init := #[]) fun acc cluster =>
      if acc.isEmpty && cluster.metas.contains mid.id then
        cluster.constraintIds
      else
        acc
    -- If not found in any cluster, fall back to direct constraints
    if clusterResult.isEmpty then
      directCids.fold (init := #[]) fun acc cid => acc.push cid
    else
      clusterResult

/-- Smart wake: only re-queue constraints related to the solved meta -/
def smartWakeBlocked (g : ConstraintGraph) (mid : MetaId) : TCM ConstraintGraph := do
  let blockedCids := g.blocked.getD mid.id #[]
  let relatedCids := g.getRelatedConstraints mid

  -- Combine blocked and related constraints
  let allCids := blockedCids ++ relatedCids

  let mut g' := { g with blocked := g.blocked.erase mid.id }
  let mut seen : HashSet Nat := {}

  for cid in allCids do
    if seen.contains cid then continue
    seen := seen.insert cid

    match g'.constraints.get? cid with
    | none => pure ()
    | some tc =>
      -- Re-compute complexity and add back to queue
      let complexity ← countUnsolvedMetas tc.metas
      g' := { g' with queue := bubbleUp (g'.queue.push (complexity, cid)) g'.queue.size }

  -- Invalidate clusters since solving may have changed relationships
  return g'.invalidateClusters

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

/-- Build the initial transient state for a solver run -/
def initialFromPostponed : TCM ConstraintGraph := do
  let allConstraints ← TCM.getPostponedTracked
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

/-- Main unified constraint solver -/
def solveConstraintGraph (tryConstraint : Constraint → TCM SolveResult)
    (fuel : Nat := constraintSolverFuel) : TCM (Array TrackedConstraint) := do
  let mut g ← ConstraintGraph.initialFromPostponed
  let mut remainingFuel := fuel

  while remainingFuel > 0 do
    remainingFuel := remainingFuel - 1

    -- Try to extract a constraint from the queue
    match g.extractMin with
    | none => break
    | some (tc, g') =>
      g := g'
      -- Try to solve this constraint
      let result ← tryConstraint tc.constraint
      match result with
      | .solved =>
        -- Successfully solved! Remove from graph
        g := g.remove tc.constraintId.id
        TCM.modifyState (·.removeConstraint tc.constraintId)
        for mid in tc.metas do
          if (← TCM.isMetaSolved mid) then
            g ← g.smartWakeBlocked mid
        let lvSols := (← TCM.getState).levelSolutions
        for lv in tc.levelVars do
          if lvSols.contains lv.id then
            g ← g.wakeBlockedOnLevelVar lv

      | .blocked metas levelVars =>
        for mid in metas do
          g := g.blockOn tc.constraintId.id mid
        for lv in levelVars do
          g := g.blockOnLevelVar tc.constraintId.id lv

      | .deferred =>
        -- Constraint couldn't make progress, re-add with same complexity
        let complexity ← ConstraintGraph.countUnsolvedMetas tc.metas
        g := { g with queue := ConstraintGraph.bubbleUp (g.queue.push (complexity, tc.constraintId.id)) g.queue.size }

      | .failed error =>
        let (chain, metas) ← g.computeMinimalUnsatisfiableSet tc
        TCM.addError (enhanceErrorWithChain error chain metas)
        g := g.remove tc.constraintId.id
        TCM.modifyState (·.removeConstraint tc.constraintId)

    let postponedSnap ← TCM.getPostponedTracked
    let mut anyNew := false
    for tc in postponedSnap do
      if !g.constraints.contains tc.constraintId.id then
        let complexity ← ConstraintGraph.countUnsolvedMetas tc.metas
        g := g.insert tc complexity
        anyNew := true
    if anyNew then
      g := g.invalidateClusters

  let mut unsolved : Array TrackedConstraint := #[]
  for (_, tc) in g.constraints do
    unsolved := unsolved.push tc
  return unsolved



end Soma.Dependent.Unify
