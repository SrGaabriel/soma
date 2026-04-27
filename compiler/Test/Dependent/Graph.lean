/-
  Test.Dependent.Graph - Tests for Constraint Graph Solver

  Tests cover:
  - Constraint clustering
  - Smart retrying
  - Speculative solving
  - Priority-based scheduling
-/

import Soma.Dependent
import Soma.Dependent.Unify.Graph
import Soma.Core.Value
import Soma.Syntax.Source
import Test.Fixtures

namespace Test.Dependent.Graph

open Test.Fixtures
open Soma.Dependent
open Soma.Dependent.Unify
open Soma.Core
open Soma.Syntax (Span)
open Std (HashMap HashSet)

/-! ## Test Infrastructure -/

def testSpan : Span := Span.uninhabited

/-- Run a TCM action and return the result or error -/
def runTCM (action : TCM α) : Except TCError (α × TCState) :=
  action.run TCContext.empty TCState.empty

/-! ## Constraint Cluster Tests -/

def mkHashSet (vals : List Nat) : HashSet Nat :=
  vals.foldl (init := {}) fun acc v => acc.insert v

def testClusterMerge : Bool :=
  let c1 : ConstraintCluster := {
    constraintIds := #[1, 2]
    metas := mkHashSet [10, 11]
    priority := 2
  }
  let c2 : ConstraintCluster := {
    constraintIds := #[3]
    metas := mkHashSet [11, 12]
    priority := 1
  }
  let merged := c1.merge c2
  merged.constraintIds.size == 3 &&
  merged.metas.contains 10 &&
  merged.metas.contains 11 &&
  merged.metas.contains 12 &&
  merged.priority == 1  -- min of 2 and 1

def testClusterOverlapsTrue : Bool :=
  let c1 : ConstraintCluster := {
    constraintIds := #[1]
    metas := mkHashSet [10, 11]
    priority := 1
  }
  let c2 : ConstraintCluster := {
    constraintIds := #[2]
    metas := mkHashSet [11, 12]
    priority := 1
  }
  c1.overlaps c2  -- Share meta 11

def testClusterOverlapsFalse : Bool :=
  let c1 : ConstraintCluster := {
    constraintIds := #[1]
    metas := mkHashSet [10]
    priority := 1
  }
  let c2 : ConstraintCluster := {
    constraintIds := #[2]
    metas := mkHashSet [20]
    priority := 1
  }
  !c1.overlaps c2  -- No shared metas

/-! ## Constraint Graph Basic Tests -/

def testGraphEmpty : Bool :=
  let g := ConstraintGraph.empty
  g.isEmpty && g.size == 0

def testGraphInsertAndSize : Bool :=
  match runTCM do
    let meta1 ← TCM.freshMeta (.vType .zero)
    let tc : TrackedConstraint := {
      constraint := .unify (.vPrimTy .int) (.vPrimTy .int) testSpan
      constraintId := ⟨0⟩
      metas := #[meta1]
      origin := .unknown
      parentConstraints := #[]
    }
    let g := ConstraintGraph.empty
    let complexity ← ConstraintGraph.countUnsolvedMetas tc.metas
    let g' := g.insert tc complexity
    return g'.size == 1 && !g'.isEmpty
  with
  | .ok (true, _) => true
  | _ => false

def testGraphRemove : Bool :=
  match runTCM do
    let meta1 ← TCM.freshMeta (.vType .zero)
    let tc : TrackedConstraint := {
      constraint := .unify (.vPrimTy .int) (.vPrimTy .int) testSpan
      constraintId := ⟨0⟩
      metas := #[meta1]
      origin := .unknown
      parentConstraints := #[]
    }
    let g := ConstraintGraph.empty
    let complexity ← ConstraintGraph.countUnsolvedMetas tc.metas
    let g' := g.insert tc complexity
    let g'' := g'.remove 0
    return g''.size == 0
  with
  | .ok (true, _) => true
  | _ => false

def testGraphExtractMin : Bool :=
  match runTCM do
    let meta1 ← TCM.freshMeta (.vType .zero)
    let meta2 ← TCM.freshMeta (.vType .zero)
    -- tc1 has 1 unsolved meta
    let tc1 : TrackedConstraint := {
      constraint := .unify (.vPrimTy .int) (.vPrimTy .int) testSpan
      constraintId := ⟨0⟩
      metas := #[meta1]
      origin := .unknown
      parentConstraints := #[]
    }
    -- tc2 has 2 unsolved metas (higher complexity)
    let tc2 : TrackedConstraint := {
      constraint := .unify (.vPrimTy .bool) (.vPrimTy .bool) testSpan
      constraintId := ⟨1⟩
      metas := #[meta1, meta2]
      origin := .unknown
      parentConstraints := #[]
    }
    let g := ConstraintGraph.empty
    let c1 ← ConstraintGraph.countUnsolvedMetas tc1.metas
    let g' := g.insert tc1 c1
    let c2 ← ConstraintGraph.countUnsolvedMetas tc2.metas
    let g'' := g'.insert tc2 c2
    -- Extract should give tc1 first (lower complexity)
    match g''.extractMin with
    | some (first, _) => return first.constraintId.id == 0
    | none => return false
  with
  | .ok (true, _) => true
  | _ => false

/-! ## Clustering Tests -/

def testBuildClustersEmpty : Bool :=
  let g := ConstraintGraph.empty
  let clusters := g.buildClusters
  clusters.isEmpty

def testBuildClustersSingleConstraint : Bool :=
  match runTCM do
    let meta1 ← TCM.freshMeta (.vType .zero)
    let tc : TrackedConstraint := {
      constraint := .unify (.vPrimTy .int) (.vPrimTy .int) testSpan
      constraintId := ⟨0⟩
      metas := #[meta1]
      origin := .unknown
      parentConstraints := #[]
    }
    let g := ConstraintGraph.empty.insert tc 1
    let clusters := g.buildClusters
    return clusters.size == 1 && clusters[0]!.constraintIds.size == 1
  with
  | .ok (true, _) => true
  | _ => false

def testBuildClustersSharedMeta : Bool :=
  match runTCM do
    let sharedMeta ← TCM.freshMeta (.vType .zero)
    let tc1 : TrackedConstraint := {
      constraint := .unify (.vPrimTy .int) (.vPrimTy .int) testSpan
      constraintId := ⟨0⟩
      metas := #[sharedMeta]
      origin := .unknown
      parentConstraints := #[]
    }
    let tc2 : TrackedConstraint := {
      constraint := .unify (.vPrimTy .bool) (.vPrimTy .bool) testSpan
      constraintId := ⟨1⟩
      metas := #[sharedMeta]  -- Same meta!
      origin := .unknown
      parentConstraints := #[]
    }
    let g := ConstraintGraph.empty.insert tc1 1 |>.insert tc2 1
    let clusters := g.buildClusters
    -- Should be merged into one cluster
    return clusters.size == 1 && clusters[0]!.constraintIds.size == 2
  with
  | .ok (true, _) => true
  | _ => false

def testBuildClustersDisjoint : Bool :=
  match runTCM do
    let meta1 ← TCM.freshMeta (.vType .zero)
    let meta2 ← TCM.freshMeta (.vType .zero)
    let tc1 : TrackedConstraint := {
      constraint := .unify (.vPrimTy .int) (.vPrimTy .int) testSpan
      constraintId := ⟨0⟩
      metas := #[meta1]
      origin := .unknown
      parentConstraints := #[]
    }
    let tc2 : TrackedConstraint := {
      constraint := .unify (.vPrimTy .bool) (.vPrimTy .bool) testSpan
      constraintId := ⟨1⟩
      metas := #[meta2]  -- Different meta
      origin := .unknown
      parentConstraints := #[]
    }
    let g := ConstraintGraph.empty.insert tc1 1 |>.insert tc2 1
    let clusters := g.buildClusters
    -- Should be two separate clusters
    return clusters.size == 2
  with
  | .ok (true, _) => true
  | _ => false

def testBuildClustersTransitive : Bool :=
  match runTCM do
    let meta1 ← TCM.freshMeta (.vType .zero)
    let meta2 ← TCM.freshMeta (.vType .zero)
    let meta3 ← TCM.freshMeta (.vType .zero)
    -- tc1 uses meta1, meta2
    let tc1 : TrackedConstraint := {
      constraint := .unify (.vPrimTy .int) (.vPrimTy .int) testSpan
      constraintId := ⟨0⟩
      metas := #[meta1, meta2]
      origin := .unknown
      parentConstraints := #[]
    }
    -- tc2 uses meta2, meta3 (shares meta2 with tc1)
    let tc2 : TrackedConstraint := {
      constraint := .unify (.vPrimTy .bool) (.vPrimTy .bool) testSpan
      constraintId := ⟨1⟩
      metas := #[meta2, meta3]
      origin := .unknown
      parentConstraints := #[]
    }
    -- tc3 uses only meta3 (transitively connected via tc2)
    let tc3 : TrackedConstraint := {
      constraint := .unify (.vPrimTy .int) (.vPrimTy .int) testSpan
      constraintId := ⟨2⟩
      metas := #[meta3]
      origin := .unknown
      parentConstraints := #[]
    }
    let g := ConstraintGraph.empty.insert tc1 2 |>.insert tc2 2 |>.insert tc3 1
    let clusters := g.buildClusters
    -- All three should be in one cluster (transitive closure)
    return clusters.size == 1 && clusters[0]!.constraintIds.size == 3
  with
  | .ok (true, _) => true
  | _ => false

/-! ## Smart Retrying Tests -/

def testGetRelatedConstraintsWithClusters : Bool :=
  match runTCM do
    let sharedMeta ← TCM.freshMeta (.vType .zero)
    let tc1 : TrackedConstraint := {
      constraint := .unify (.vPrimTy .int) (.vPrimTy .int) testSpan
      constraintId := ⟨0⟩
      metas := #[sharedMeta]
      origin := .unknown
      parentConstraints := #[]
    }
    let tc2 : TrackedConstraint := {
      constraint := .unify (.vPrimTy .bool) (.vPrimTy .bool) testSpan
      constraintId := ⟨1⟩
      metas := #[sharedMeta]
      origin := .unknown
      parentConstraints := #[]
    }
    let g := ConstraintGraph.empty.insert tc1 1 |>.insert tc2 1
    -- Compute clusters
    let (g', _) := g.getClusters
    -- Get related constraints for the shared meta
    let related := g'.getRelatedConstraints sharedMeta
    -- Should return both constraints
    return related.size == 2
  with
  | .ok (true, _) => true
  | _ => false

def testGetRelatedConstraintsNoClusters : Bool :=
  match runTCM do
    let meta1 ← TCM.freshMeta (.vType .zero)
    let tc1 : TrackedConstraint := {
      constraint := .unify (.vPrimTy .int) (.vPrimTy .int) testSpan
      constraintId := ⟨0⟩
      metas := #[meta1]
      origin := .unknown
      parentConstraints := #[]
    }
    let g := ConstraintGraph.empty.insert tc1 1
    -- Don't compute clusters - should fall back to direct lookup
    let related := g.getRelatedConstraints meta1
    return related.size == 1
  with
  | .ok (true, _) => true
  | _ => false

def testSmartWakeBlocked : Bool :=
  match runTCM do
    let meta1 ← TCM.freshMeta (.vType .zero)
    let tc1 : TrackedConstraint := {
      constraint := .unify (.vPrimTy .int) (.vPrimTy .int) testSpan
      constraintId := ⟨0⟩
      metas := #[meta1]
      origin := .unknown
      parentConstraints := #[]
    }
    let g := ConstraintGraph.empty.insert tc1 1
    -- Block the constraint on the meta
    let g' := g.blockOn 0 meta1
    -- Smart wake should re-add it to the queue
    let g'' ← g'.smartWakeBlocked meta1
    -- Queue should not be empty
    return !g''.queue.isEmpty
  with
  | .ok (true, _) => true
  | _ => false

def testInvalidateClusters : Bool :=
  match runTCM do
    let meta1 ← TCM.freshMeta (.vType .zero)
    let tc1 : TrackedConstraint := {
      constraint := .unify (.vPrimTy .int) (.vPrimTy .int) testSpan
      constraintId := ⟨0⟩
      metas := #[meta1]
      origin := .unknown
      parentConstraints := #[]
    }
    let g := ConstraintGraph.empty.insert tc1 1
    let (g', _) := g.getClusters
    -- Clusters should be cached
    let hasClusters1 := g'.clusters.isSome
    -- Invalidate
    let g'' := g'.invalidateClusters
    let hasClusters2 := g''.clusters.isSome
    return hasClusters1 && !hasClusters2
  with
  | .ok (true, _) => true
  | _ => false

/-! ## Cluster Sorting Tests -/

def testSortClustersBySize : Bool :=
  let small : ConstraintCluster := {
    constraintIds := #[1]
    metas := {}
    priority := 1
  }
  let medium : ConstraintCluster := {
    constraintIds := #[2, 3]
    metas := {}
    priority := 2
  }
  let large : ConstraintCluster := {
    constraintIds := #[4, 5, 6]
    metas := {}
    priority := 3
  }
  let clusters := #[large, small, medium]
  let ascending := ConstraintGraph.sortClustersBySize clusters true
  let descending := ConstraintGraph.sortClustersBySize clusters false
  ascending[0]!.constraintIds.size == 1 &&
  ascending[2]!.constraintIds.size == 3 &&
  descending[0]!.constraintIds.size == 3 &&
  descending[2]!.constraintIds.size == 1

/-! ## Strategy Tests -/

def testWithStrategy : Bool :=
  let g := ConstraintGraph.empty
  let g' := g.withStrategy .smallestClusterFirst
  g'.strategy == .smallestClusterFirst

/-! ## Integration Tests -/

def testSolveConstraintGraphBasic : Bool :=
  match runTCM do
    -- Create a simple solvable constraint
    let constraint := Constraint.unify (.vPrimTy .int) (.vPrimTy .int) testSpan
    TCM.postpone constraint
    -- Solve it
    let remaining ← solveConstraintGraph trySolveBasicConstraint
    return remaining.isEmpty
  with
  | .ok (true, _) => true
  | _ => false

def testSolveConstraintGraphWithMeta : Bool :=
  match runTCM do
    -- Create a meta and unify with a concrete type
    let metaVal ← TCM.freshMetaVal (.vType .zero)
    let metas := Value.collectMetas metaVal
    let constraint := Constraint.unify metaVal (.vPrimTy .int) testSpan
    let _ ← TCM.postponeTracked constraint metas
    -- Solve
    let remaining ← solveConstraintGraph trySolveBasicConstraint
    -- The meta should be solved
    let metaVal' ← force metaVal
    match metaVal' with
    | .vPrimTy .int => return remaining.isEmpty
    | _ => return false
  with
  | .ok (true, _) => true
  | _ => false

def testSolveConstraintGraphMultiple : Bool :=
  match runTCM do
    -- Create multiple constraints
    let meta1 ← TCM.freshMetaVal (.vType .zero)
    let meta2 ← TCM.freshMetaVal (.vType .zero)
    let c1 := Constraint.unify meta1 (.vPrimTy .int) testSpan
    let c2 := Constraint.unify meta2 (.vPrimTy .bool) testSpan
    let _ ← TCM.postponeTracked c1 (Value.collectMetas meta1)
    let _ ← TCM.postponeTracked c2 (Value.collectMetas meta2)
    -- Solve
    let remaining ← solveConstraintGraph trySolveBasicConstraint
    -- Both should be solved
    let m1 ← force meta1
    let m2 ← force meta2
    match m1, m2 with
    | .vPrimTy .int, .vPrimTy .bool => return remaining.isEmpty
    | _, _ => return false
  with
  | .ok (true, _) => true
  | _ => false

def testSolveConstraintGraphClustered : Bool :=
  match runTCM do
    -- Create constraints that share a meta (will be clustered)
    let sharedMeta ← TCM.freshMetaVal (.vType .zero)
    let c1 := Constraint.unify sharedMeta (.vPrimTy .int) testSpan
    let c2 := Constraint.unify sharedMeta (.vPrimTy .int) testSpan
    let _ ← TCM.postponeTracked c1 (Value.collectMetas sharedMeta)
    let _ ← TCM.postponeTracked c2 (Value.collectMetas sharedMeta)
    -- Solve using clustered strategy
    let remaining ← solveConstraintGraphClustered trySolveBasicConstraint .smallestClusterFirst
    return remaining.isEmpty
  with
  | .ok (true, _) => true
  | _ => false

/-! ## Test Lists -/

def clusterTests : List (String × Bool) := [
  ("cluster merge", testClusterMerge),
  ("cluster overlaps true", testClusterOverlapsTrue),
  ("cluster overlaps false", testClusterOverlapsFalse)
]

def graphBasicTests : List (String × Bool) := [
  ("graph empty", testGraphEmpty),
  ("graph insert and size", testGraphInsertAndSize),
  ("graph remove", testGraphRemove),
  ("graph extractMin priority", testGraphExtractMin)
]

def clusteringTests : List (String × Bool) := [
  ("build clusters empty", testBuildClustersEmpty),
  ("build clusters single", testBuildClustersSingleConstraint),
  ("build clusters shared meta", testBuildClustersSharedMeta),
  ("build clusters disjoint", testBuildClustersDisjoint),
  ("build clusters transitive", testBuildClustersTransitive)
]

def smartRetryTests : List (String × Bool) := [
  ("get related with clusters", testGetRelatedConstraintsWithClusters),
  ("get related no clusters", testGetRelatedConstraintsNoClusters),
  ("smart wake blocked", testSmartWakeBlocked),
  ("invalidate clusters", testInvalidateClusters)
]

def sortingTests : List (String × Bool) := [
  ("sort clusters by size", testSortClustersBySize)
]

def strategyTests : List (String × Bool) := [
  ("with strategy", testWithStrategy)
]

def integrationTests : List (String × Bool) := [
  ("solve basic", testSolveConstraintGraphBasic),
  ("solve with meta", testSolveConstraintGraphWithMeta),
  ("solve multiple", testSolveConstraintGraphMultiple),
  ("solve clustered", testSolveConstraintGraphClustered)
]

def runTestGroup (name : String) (tests : List (String × Bool)) : IO TestRunner := do
  IO.println s!"  === {name} ==="
  let mut runner := TestRunner.init
  for (testName, result) in tests do
    if result then
      runner := runner.recordPass
    else
      IO.println s!"    FAILED: {testName}"
      runner := runner.recordFail testName
  IO.println s!"    Passed: {runner.passed}, Failed: {runner.failed}"
  return runner

def run : IO TestRunner := do
  IO.println "=== Constraint Graph Tests ===\n"

  let mut combined := TestRunner.init

  let r1 ← runTestGroup "Cluster Structure" clusterTests
  combined := combined.merge r1

  let r2 ← runTestGroup "Graph Basics" graphBasicTests
  combined := combined.merge r2

  let r3 ← runTestGroup "Clustering" clusteringTests
  combined := combined.merge r3

  let r4 ← runTestGroup "Smart Retrying" smartRetryTests
  combined := combined.merge r4

  let r5 ← runTestGroup "Sorting" sortingTests
  combined := combined.merge r5

  let r6 ← runTestGroup "Strategy" strategyTests
  combined := combined.merge r6

  let r7 ← runTestGroup "Integration" integrationTests
  combined := combined.merge r7

  IO.println s!"\nTotal: {combined.passed} passed, {combined.failed} failed"

  if combined.failed > 0 then
    IO.println "\nFAILURES:"
    for f in combined.failures do IO.println s!"  - {f}"

  return combined

end Test.Dependent.Graph
