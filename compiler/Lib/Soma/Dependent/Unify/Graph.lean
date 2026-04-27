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

/-- Merge two clusters -/
def merge (c1 c2 : ConstraintCluster) : ConstraintCluster :=
  { constraintIds := c1.constraintIds ++ c2.constraintIds
  , metas := c2.metas.fold (init := c1.metas) fun acc mid => acc.insert mid
  , priority := min c1.priority c2.priority }

/-- Check if two clusters share any metas -/
def overlaps (c1 c2 : ConstraintCluster) : Bool :=
  c1.metas.fold (init := false) fun acc mid =>
    acc || c2.metas.contains mid

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

/-- Check if the graph has no pending constraints -/
def isEmpty (g : ConstraintGraph) : Bool :=
  g.queue.isEmpty && g.blocked.isEmpty && g.blockedOnLevelVar.isEmpty

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

/-- Wake up constraints blocked on a meta (re-add to queue) -/
def wakeBlocked (g : ConstraintGraph) (mid : MetaId) : TCM ConstraintGraph := do
  let blockedCids := g.blocked.getD mid.id #[]
  let mut g' := { g with blocked := g.blocked.erase mid.id }
  for cid in blockedCids do
    match g'.constraints.get? cid with
    | none => pure ()
    | some tc =>
      let complexity ← countUnsolvedMetas tc.metas
      g' := { g' with queue := bubbleUp (g'.queue.push (complexity, cid)) g'.queue.size }
  return g'

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

/-- Make a `metaId → SCC index` map -/
def metaSCCIndices (metas : Soma.Core.MetaState) : HashMap Nat Nat := Id.run do
  let graph := buildMetaDepGraph metas
  let nodes := metas.metas.toArray.map (·.1)
  let sccs := TarjanSCC.run graph nodes
  let mut acc : HashMap Nat Nat := {}
  for h : i in [:sccs.size] do
    for m in sccs[i]'h.upper do
      acc := acc.insert m i
  return acc

/-- Build clusters of related constraints using BFS over the constraint–meta graph -/
def buildClusters (g : ConstraintGraph) (sccIdx : HashMap Nat Nat := {}) : Array ConstraintCluster :=
  -- Phase 1: Build meta -> constraints mapping
  let emptyM2C : HashMap Nat (Array Nat) := {}
  let metaToConstraints := g.constraints.fold (init := emptyM2C)
    fun acc cid tc =>
      tc.metas.foldl (init := acc) fun acc' mid =>
        let existing := acc'.getD mid.id #[]
        acc'.insert mid.id (existing.push cid)

  -- Phase 2: Build clusters using BFS from each unvisited constraint
  let emptyVisited : HashSet Nat := {}
  let emptyResult : Array ConstraintCluster := #[]

  let (result, _) := g.constraints.fold (init := (emptyResult, emptyVisited))
    fun (clusters, visited) startCid _ =>
      if visited.contains startCid then (clusters, visited)
      else
        -- BFS to find all connected constraints
        let (clusterCids, clusterMetas, visited') :=
          bfsCluster g metaToConstraints startCid visited
        if clusterCids.isEmpty then (clusters, visited')
        else
          let scc := clusterMetas.fold (init := none) fun (acc : Option Nat) mid =>
            match sccIdx.get? mid with
            | some i =>
              match acc with
              | some j => some (min i j)
              | none => some i
            | none => acc
          let priority : Nat :=
            match scc with
            | some i => i * (g.constraints.size + 1) + clusterCids.size
            | none   => clusterCids.size
          let cluster : ConstraintCluster := {
            constraintIds := clusterCids
            metas := clusterMetas
            priority := priority
          }
          (clusters.push cluster, visited')

  -- Sort by priority
  result.qsort fun c1 c2 => c1.priority < c2.priority
where
  /-- BFS to find all constraints connected to startCid via shared metas.
      Uses fuel to ensure termination. -/
  bfsCluster (g : ConstraintGraph) (m2c : HashMap Nat (Array Nat))
      (startCid : Nat) (visited : HashSet Nat)
      : Array Nat × HashSet Nat × HashSet Nat :=
    let emptyQueue : Array Nat := #[startCid]
    let emptyMetas : HashSet Nat := {}
    -- Use fuel = total constraints as upper bound on iterations
    let fuel := g.constraints.size + 1
    go fuel g m2c emptyQueue #[] emptyMetas visited
  go (fuel : Nat) (g : ConstraintGraph) (m2c : HashMap Nat (Array Nat))
      (queue : Array Nat) (result : Array Nat) (metas : HashSet Nat)
      (visited : HashSet Nat) : Array Nat × HashSet Nat × HashSet Nat :=
    match fuel with
    | 0 => (result, metas, visited)  -- Out of fuel
    | fuel' + 1 =>
      if h : queue.size > 0 then
        let cid := queue[0]'h
        let queue' := queue.extract 1 queue.size
        if visited.contains cid then
          go fuel' g m2c queue' result metas visited
        else
          let visited' := visited.insert cid
          match g.constraints.get? cid with
          | none => go fuel' g m2c queue' result metas visited'
          | some tc =>
            let result' := result.push cid
            -- Add all metas from this constraint
            let metas' := tc.metas.foldl (init := metas) fun acc mid =>
              acc.insert mid.id
            -- Add all constraints that share these metas to the queue
            let queue'' := tc.metas.foldl (init := queue') fun q mid =>
              let related := m2c.getD mid.id #[]
              related.foldl (init := q) fun q' rcid =>
                if visited'.contains rcid then q' else q'.push rcid
            go fuel' g m2c queue'' result' metas' visited'
      else
        (result, metas, visited)

/-- Get or compute clusters -/
def getClusters (g : ConstraintGraph) (sccIdx : HashMap Nat Nat := {})
    : ConstraintGraph × Array ConstraintCluster :=
  match g.clusters with
  | some clusters => (g, clusters)
  | none =>
    let clusters := g.buildClusters sccIdx
    ({ g with clusters := some clusters }, clusters)

/-- Invalidate cached clusters (call when constraints change) -/
def invalidateClusters (g : ConstraintGraph) : ConstraintGraph :=
  { g with clusters := none }

/-- Set the solving strategy -/
def withStrategy (g : ConstraintGraph) (s : SolveStrategy) : ConstraintGraph :=
  { g with strategy := s }

/-! ### Smart Retrying -/

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

/-! ### Cluster-based Solving -/

/-- Extract next constraint from a specific cluster -/
def extractFromCluster (g : ConstraintGraph) (cluster : ConstraintCluster)
    : Option (TrackedConstraint × ConstraintGraph) := Id.run do
  -- Find the constraint with minimum complexity in this cluster
  let mut minComplexity : Option (Nat × Nat) := none  -- (complexity, cid)

  for cid in cluster.constraintIds do
    match g.constraints.get? cid with
    | none => continue
    | some tc =>
      let complexity := tc.metas.size
      match minComplexity with
      | none => minComplexity := some (complexity, cid)
      | some (minC, _) =>
        if complexity < minC then
          minComplexity := some (complexity, cid)

  match minComplexity with
  | none => return none
  | some (_, cid) =>
    match g.constraints.get? cid with
    | none => return none
    | some tc => return some (tc, g)

/-- Sort clusters by size for cluster-first strategies -/
def sortClustersBySize (clusters : Array ConstraintCluster) (ascending : Bool)
    : Array ConstraintCluster :=
  let sorted := clusters.qsort fun c1 c2 =>
    if ascending then
      c1.constraintIds.size < c2.constraintIds.size
    else
      c1.constraintIds.size > c2.constraintIds.size
  sorted

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

/-- Creates a cluster from initial postponed state of related constraints and solves them together -/
def solveConstraintGraphClustered (tryConstraint : Constraint → TCM SolveResult)
    (strategy : SolveStrategy := .smallestClusterFirst)
    (fuel : Nat := constraintSolverFuel) : TCM (Array TrackedConstraint) := do
  let mut g ← ConstraintGraph.initialFromPostponed
  g := g.withStrategy strategy

  let mut remainingFuel := fuel

  let tcState ← TCM.getState
  let sccIdx := ConstraintGraph.metaSCCIndices tcState.metas

  -- Build initial clusters
  let (g', initialClusters) := g.getClusters sccIdx
  g := g'

  -- Sort clusters based on strategy
  let sortedClusters := match strategy with
    | .priority => initialClusters
    | .smallestClusterFirst => ConstraintGraph.sortClustersBySize initialClusters true
    | .largestClusterFirst => ConstraintGraph.sortClustersBySize initialClusters false

  -- Process clusters in order
  for cluster in sortedClusters do
    -- Solve all constraints in this cluster
    for cid in cluster.constraintIds do
      if remainingFuel == 0 then break
      remainingFuel := remainingFuel - 1

      match g.constraints.get? cid with
      | none => continue
      | some tc =>
        let result ← tryConstraint tc.constraint
        match result with
        | .solved =>
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
          let complexity ← ConstraintGraph.countUnsolvedMetas tc.metas
          g := { g with queue := ConstraintGraph.bubbleUp (g.queue.push (complexity, cid)) g.queue.size }

        | .failed error =>
          let (chain, metas) ← g.computeMinimalUnsatisfiableSet tc
          TCM.addError (enhanceErrorWithChain error chain metas)
          g := g.remove tc.constraintId.id
          TCM.modifyState (·.removeConstraint tc.constraintId)

      let postponedSnap ← TCM.getPostponedTracked
      let mut anyNew := false
      for ntc in postponedSnap do
        if !g.constraints.contains ntc.constraintId.id then
          let complexity ← ConstraintGraph.countUnsolvedMetas ntc.metas
          g := g.insert ntc complexity
          anyNew := true
      if anyNew then g := g.invalidateClusters

  if !g.isEmpty then
    return ← solveConstraintGraph tryConstraint remainingFuel

  let mut unsolved : Array TrackedConstraint := #[]
  for (_, tc) in g.constraints do
    unsolved := unsolved.push tc
  return unsolved

/-- Multiple solving strategies with rollback -/
def solveConstraintGraphSpeculative (tryConstraint : Constraint → TCM SolveResult)
    (fuel : Nat := constraintSolverFuel) : TCM (Array TrackedConstraint) := do
  let initialState ← TCM.getState
  let initialSize := initialState.postponed.size

  let runStrategy (action : TCM (Array TrackedConstraint))
      : TCM (Option (Array TrackedConstraint × Nat × Nat × TCState)) := do
    set initialState
    match ← TCM.tryWithRollback action with
    | some r =>
      let st ← TCM.getState
      return some (r, r.size, st.errors.size, st)
    | none => return none

  let result1 ← runStrategy (solveConstraintGraph tryConstraint fuel)
  let result2 ← runStrategy (solveConstraintGraphClustered tryConstraint .smallestClusterFirst fuel)
  let result3 ← runStrategy (solveConstraintGraphClustered tryConstraint .largestClusterFirst fuel)

  let mut bestRemaining := initialSize
  let mut bestErrors := initialSize
  let mut bestResult : Option (Array TrackedConstraint) := none
  let mut bestState := initialState
  for r in [result1, result2, result3] do
    match r with
    | some (arr, rem, errs, st) =>
      if errs < bestErrors || (errs == bestErrors && rem < bestRemaining) then
        bestRemaining := rem
        bestErrors := errs
        bestResult := some arr
        bestState := st
    | none => pure ()

  set bestState
  match bestResult with
  | some r => return r
  | none =>
    -- All strategies failed, fall back to default
    set initialState
    solveConstraintGraph tryConstraint fuel

end Soma.Dependent.Unify
