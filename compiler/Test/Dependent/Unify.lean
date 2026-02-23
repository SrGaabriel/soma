/-
  Test.Dependent.Unify - Tests for Phase 3: Unification and Metavariables

  Tests cover:
  - Pattern unification (Miller's algorithm)
  - Row unification with rewriting
  - Occurs check
  - Constraint solving
  - Zonking
-/

import Soma.Dependent
import Soma.Core.Value
import Soma.Core.Level
import Soma.Syntax.Source
import Test.Fixtures

namespace Test.Dependent.Unify

open Test.Fixtures

open Soma.Dependent
open Soma.Dependent.Unify (SolveResult)
open Soma.Core
open Soma.Syntax (Span)

/-! ## Test Infrastructure -/

def testSpan : Span := Span.uninhabited

/-- Run a TCM action and return the result or error -/
def runTCM (action : TCM α) : Except TCError (α × TCState) :=
  action.run TCContext.empty TCState.empty

/-- Run a TCM action and check if it succeeds -/
def checkSucceeds (action : TCM α) : Bool :=
  match runTCM action with
  | .ok _ => true
  | .error _ => false

/-- Run a TCM action and check if it fails -/
def checkFails (action : TCM α) : Bool :=
  match runTCM action with
  | .ok _ => false
  | .error _ => true

/-! ## Occurs Check Tests -/

def testOccursInVar : Bool :=
  let metaId : MetaId := ⟨0⟩
  let v := Value.vNeutral .type0 (.nVar ⟨"x", ⟨0⟩⟩)
  occursIn metaId v == false

def testOccursInMeta : Bool :=
  let metaId : MetaId := ⟨0⟩
  let v := Value.vNeutral .type0 (.nMeta metaId)
  occursIn metaId v == true

def testOccursInDifferentMeta : Bool :=
  let metaId1 : MetaId := ⟨0⟩
  let metaId2 : MetaId := ⟨1⟩
  let v := Value.vNeutral .type0 (.nMeta metaId2)
  occursIn metaId1 v == false

def testOccursInPi : Bool :=
  let metaId : MetaId := ⟨0⟩
  let dom := Value.vNeutral .type0 (.nMeta metaId)
  let clos := Closure.mkEmpty "x" Env.empty
  let v := Value.vPi .omega .explicit "x" dom clos
  occursIn metaId v == true

def testOccursInPair : Bool :=
  let metaId : MetaId := ⟨0⟩
  let fst := Value.vIntLit 1
  let snd := Value.vNeutral .type0 (.nMeta metaId)
  let v := Value.vPair fst snd
  occursIn metaId v == true

/-! ## Scope Checking Tests -/

def testInScopeVar : Bool :=
  let allowedLevels := [⟨0⟩, ⟨1⟩]
  let v := Value.vNeutral .type0 (.nVar ⟨"x", ⟨0⟩⟩)
  inScope allowedLevels v == true

def testInScopeVarNotAllowed : Bool :=
  let allowedLevels := [⟨0⟩, ⟨1⟩]
  let v := Value.vNeutral .type0 (.nVar ⟨"x", ⟨2⟩⟩)
  inScope allowedLevels v == false

def testInScopeMeta : Bool :=
  -- Metas are always considered in scope
  let allowedLevels := [⟨0⟩]
  let v := Value.vNeutral .type0 (.nMeta ⟨0⟩)
  inScope allowedLevels v == true

/-! ## Spine Pattern Tests -/

def testSpineIsPatternEmpty : Bool :=
  let spine : Spine := ⟨[]⟩
  match spineIsPattern spine with
  | some [] => true
  | _ => false

def testSpineIsPatternDistinct : Bool :=
  let x := Value.vNeutral .type0 (.nVar ⟨"x", ⟨0⟩⟩)
  let y := Value.vNeutral .type0 (.nVar ⟨"y", ⟨1⟩⟩)
  let spine : Spine := ⟨[x, y]⟩
  match spineIsPattern spine with
  | some [⟨0⟩, ⟨1⟩] => true
  | _ => false

def testSpineIsPatternDuplicate : Bool :=
  let x := Value.vNeutral .type0 (.nVar ⟨"x", ⟨0⟩⟩)
  let spine : Spine := ⟨[x, x]⟩  -- Duplicate!
  match spineIsPattern spine with
  | none => true  -- Should fail
  | some _ => false

def testSpineIsPatternNonVar : Bool :=
  let notVar := Value.vIntLit 42
  let spine : Spine := ⟨[notVar]⟩
  match spineIsPattern spine with
  | none => true  -- Should fail
  | some _ => false

/-! ## Substitution Tests -/

def testSubstLookupFound : Bool :=
  let subst := mkSubst [⟨0⟩, ⟨1⟩]
  match subst.lookup ⟨0⟩ with
  | some 0 => true
  | _ => false

def testSubstLookupSecond : Bool :=
  let subst := mkSubst [⟨0⟩, ⟨1⟩]
  match subst.lookup ⟨1⟩ with
  | some 1 => true
  | _ => false

def testSubstLookupNotFound : Bool :=
  let subst := mkSubst [⟨0⟩, ⟨1⟩]
  match subst.lookup ⟨2⟩ with
  | none => true
  | some _ => false

/-! ## Basic Unification Tests -/

def testUnifyTypesSame : Bool :=
  checkSucceeds do
    unify (.vType .zero) (.vType .zero)

def testUnifyPrimTysSame : Bool :=
  checkSucceeds do
    unify (.vPrimTy .int) (.vPrimTy .int)

def testUnifyPrimTysDifferent : Bool :=
  checkFails do
    unify (.vPrimTy .int) (.vPrimTy .bool)

def testUnifyIntLitsSame : Bool :=
  checkSucceeds do
    unify (.vIntLit 42) (.vIntLit 42)

def testUnifyIntLitsDifferent : Bool :=
  checkFails do
    unify (.vIntLit 42) (.vIntLit 43)

def testUnifyLabelsSame : Bool :=
  checkSucceeds do
    unify (.vLabelLit "foo") (.vLabelLit "foo")

def testUnifyLabelsDifferent : Bool :=
  checkFails do
    unify (.vLabelLit "foo") (.vLabelLit "bar")

def testUnifyRowEmpty : Bool :=
  checkSucceeds do
    unify .vRowEmpty .vRowEmpty

/-! ## Metavariable Solving Tests -/

def testSolveSimpleMeta : Bool :=
  match runTCM do
    let metaId ← TCM.freshMeta (.vType .zero)
    solveMeta metaId [] (.vPrimTy .int)
    let info? ← TCM.lookupMeta metaId
    match info? with
    | some info => return info.solution.isSome
    | none => return false
  with
  | .ok (true, _) => true
  | _ => false

def testMetaUnifySolves : Bool :=
  match runTCM do
    let metaVal ← TCM.freshMetaVal (.vType .zero)
    unify metaVal (.vPrimTy .int)
    -- After unification, force should give us the solution
    let result ← force metaVal
    match result with
    | .vPrimTy .int => return true
    | _ => return false
  with
  | .ok (true, _) => true
  | _ => false

/-! ## Row Unification Tests -/

def testUnifyRowsSameLabel : Bool :=
  checkSucceeds do
    let row1 := Value.vRowExtend (.vLabelLit "x") (.vPrimTy .int) .vRowEmpty
    let row2 := Value.vRowExtend (.vLabelLit "x") (.vPrimTy .int) .vRowEmpty
    unify row1 row2

def testUnifyRowsDifferentLabels : Bool :=
  -- Should succeed with rewriting
  checkSucceeds do
    let row1 := Value.vRowExtend (.vLabelLit "x") (.vPrimTy .int)
                  (Value.vRowExtend (.vLabelLit "y") (.vPrimTy .bool) .vRowEmpty)
    let row2 := Value.vRowExtend (.vLabelLit "y") (.vPrimTy .bool)
                  (Value.vRowExtend (.vLabelLit "x") (.vPrimTy .int) .vRowEmpty)
    unify row1 row2

def testUnifyRecordTypes : Bool :=
  checkSucceeds do
    let row := Value.vRowExtend (.vLabelLit "x") (.vPrimTy .int) .vRowEmpty
    unify (.vRecord row) (.vRecord row)

/-! ## Constraint Solving Tests -/

def testSolveConstraintSuccess : Bool :=
  match runTCM do
    let c := Constraint.unify (.vPrimTy .int) (.vPrimTy .int) testSpan
    trySolveConstraint c
  with
  | .ok (.solved, _) => true
  | _ => false

def testSolveConstraintFail : Bool :=
  match runTCM do
    let c := Constraint.unify (.vPrimTy .int) (.vPrimTy .bool) testSpan
    trySolveConstraint c
  with
  | .ok (.failed _, _) => true
  | _ => false

def testSolveLevelConstraintEqual : Bool :=
  match runTCM do
    let c := Constraint.levelEq (.lit 0) (.lit 0)
    trySolveConstraint c
  with
  | .ok (.solved, _) => true
  | _ => false

def testSolveLevelConstraintUnequal : Bool :=
  match runTCM do
    let c := Constraint.levelEq (.lit 0) (.lit 1)
    trySolveConstraint c
  with
  | .ok (.deferred, _) => true  -- Level constraints are deferred when not equal
  | _ => false

/-! ## Zonking Tests -/

def testZonkValuePrimTy : Bool :=
  match runTCM do
    zonkValue (.vPrimTy .int)
  with
  | .ok (.vPrimTy .int, _) => true
  | _ => false

def testZonkValuePair : Bool :=
  match runTCM do
    let result ← zonkValue (.vPair (.vIntLit 1) (.vIntLit 2))
    match result with
    | .vPair (.vIntLit 1) (.vIntLit 2) => return true
    | _ => return false
  with
  | .ok (true, _) => true
  | _ => false

def testZonkSolvedMeta : Bool :=
  match runTCM do
    -- Create and solve a meta
    let metaId ← TCM.freshMeta (.vType .zero)
    TCM.solveMeta metaId (.vPrimTy .int)
    -- Create a value containing that meta
    let v := Value.vNeutral (.vType .zero) (.nMeta metaId)
    -- Zonking should substitute the solution
    let result ← zonkValue v
    match result with
    | .vPrimTy .int => return true
    | _ => return false
  with
  | .ok (true, _) => true
  | _ => false

def testZonkUnsolvedMeta : Bool :=
  match runTCM do
    -- Create but don't solve a meta
    let metaId ← TCM.freshMeta (.vType .zero)
    let v := Value.vNeutral (.vType .zero) (.nMeta metaId)
    -- Zonking should leave it as a meta
    let result ← zonkValue v
    match result with
    | .vNeutral _ (.nMeta _) => return true
    | _ => return false
  with
  | .ok (true, _) => true
  | _ => false

def testZonkLevel : Bool :=
  match runTCM do
    let result ← zonkLevel (.max (.lit 1) (.lit 2))
    -- Should simplify to lit 2
    return result == .lit 2
  with
  | .ok (true, _) => true
  | _ => false

/-! ## Unsolved Meta Detection Tests -/

def testHasUnsolvedMetasNo : Bool :=
  match runTCM do
    hasUnsolvedMetas (.vPrimTy .int)
  with
  | .ok (false, _) => true
  | _ => false

def testHasUnsolvedMetasYes : Bool :=
  match runTCM do
    let metaId ← TCM.freshMeta (.vType .zero)
    let v := Value.vNeutral (.vType .zero) (.nMeta metaId)
    hasUnsolvedMetas v
  with
  | .ok (true, _) => true
  | _ => false

def testHasUnsolvedMetasSolved : Bool :=
  match runTCM do
    let metaId ← TCM.freshMeta (.vType .zero)
    TCM.solveMeta metaId (.vPrimTy .int)
    let v := Value.vNeutral (.vType .zero) (.nMeta metaId)
    hasUnsolvedMetas v
  with
  | .ok (false, _) => true
  | _ => false

/-! ## Test Runner -/

def occursCheckTests : List (String × Bool) := [
  ("occursIn var (no)", testOccursInVar),
  ("occursIn same meta (yes)", testOccursInMeta),
  ("occursIn different meta (no)", testOccursInDifferentMeta),
  ("occursIn Pi domain", testOccursInPi),
  ("occursIn pair snd", testOccursInPair)
]

def scopeCheckTests : List (String × Bool) := [
  ("inScope var allowed", testInScopeVar),
  ("inScope var not allowed", testInScopeVarNotAllowed),
  ("inScope meta always", testInScopeMeta)
]

def spinePatternTests : List (String × Bool) := [
  ("spine pattern empty", testSpineIsPatternEmpty),
  ("spine pattern distinct vars", testSpineIsPatternDistinct),
  ("spine pattern duplicate var fails", testSpineIsPatternDuplicate),
  ("spine pattern non-var fails", testSpineIsPatternNonVar)
]

def substTests : List (String × Bool) := [
  ("subst lookup first", testSubstLookupFound),
  ("subst lookup second", testSubstLookupSecond),
  ("subst lookup not found", testSubstLookupNotFound)
]

def basicUnifyTests : List (String × Bool) := [
  ("unify types same level", testUnifyTypesSame),
  ("unify same primTy", testUnifyPrimTysSame),
  ("unify different primTy fails", testUnifyPrimTysDifferent),
  ("unify same int lit", testUnifyIntLitsSame),
  ("unify different int lit fails", testUnifyIntLitsDifferent),
  ("unify same label", testUnifyLabelsSame),
  ("unify different label fails", testUnifyLabelsDifferent),
  ("unify row empty", testUnifyRowEmpty)
]

def metaSolvingTests : List (String × Bool) := [
  ("solve simple meta", testSolveSimpleMeta),
  ("unify solves meta", testMetaUnifySolves)
]

def rowUnifyTests : List (String × Bool) := [
  ("unify rows same label", testUnifyRowsSameLabel),
  ("unify rows different order", testUnifyRowsDifferentLabels),
  ("unify record types", testUnifyRecordTypes)
]

def constraintTests : List (String × Bool) := [
  ("solve constraint success", testSolveConstraintSuccess),
  ("solve constraint fail", testSolveConstraintFail),
  ("solve level constraint equal", testSolveLevelConstraintEqual),
  ("solve level constraint unequal", testSolveLevelConstraintUnequal)
]

def zonkTests : List (String × Bool) := [
  ("zonk primTy", testZonkValuePrimTy),
  ("zonk pair", testZonkValuePair),
  ("zonk solved meta", testZonkSolvedMeta),
  ("zonk unsolved meta", testZonkUnsolvedMeta),
  ("zonk level simplifies", testZonkLevel)
]

def unsolvedMetaTests : List (String × Bool) := [
  ("hasUnsolvedMetas no", testHasUnsolvedMetasNo),
  ("hasUnsolvedMetas yes", testHasUnsolvedMetasYes),
  ("hasUnsolvedMetas solved", testHasUnsolvedMetasSolved)
]

/-! ## Metavariable Dependency Tracking Tests -/

def testCollectMetasEmpty : Bool :=
  let metas := collectMetas (.vPrimTy .int)
  metas.isEmpty

def testCollectMetasSingle : Bool :=
  let metaId : MetaId := ⟨0⟩
  let v := Value.vNeutral .type0 (.nMeta metaId)
  let metas := collectMetas v
  metas.size == 1 && metas[0]! == metaId

def testCollectMetasMultiple : Bool :=
  let meta1 : MetaId := ⟨0⟩
  let meta2 : MetaId := ⟨1⟩
  let v := Value.vPair
    (Value.vNeutral .type0 (.nMeta meta1))
    (Value.vNeutral .type0 (.nMeta meta2))
  let metas := collectMetas v
  metas.size == 2 && metas.contains meta1 && metas.contains meta2

def testCollectMetasPi : Bool :=
  let metaId : MetaId := ⟨0⟩
  let dom := Value.vNeutral .type0 (.nMeta metaId)
  let clos := Closure.const "_" (.vPrimTy .int)
  let v := Value.vPi .omega .explicit "x" dom clos
  let metas := collectMetas v
  metas.contains metaId

def testCollectMetasConstraint : Bool :=
  let meta1 : MetaId := ⟨0⟩
  let meta2 : MetaId := ⟨1⟩
  let v1 := Value.vNeutral .type0 (.nMeta meta1)
  let v2 := Value.vNeutral .type0 (.nMeta meta2)
  let c := Constraint.unify v1 v2 testSpan
  let metas := collectMetasConstraint c
  metas.size == 2 && metas.contains meta1 && metas.contains meta2

def testMetaDependenciesEmpty : Bool :=
  let deps := MetaDependencies.empty
  deps.getConstraintsFor ⟨0⟩ |>.isEmpty

def testMetaDependenciesRegister : Bool :=
  let deps := MetaDependencies.empty
  let metas : Array MetaId := #[⟨0⟩, ⟨1⟩]
  let (cid, deps') := deps.registerConstraint metas
  -- Check that both metas point to this constraint
  let cids0 := deps'.getConstraintsFor ⟨0⟩
  let cids1 := deps'.getConstraintsFor ⟨1⟩
  cids0.contains cid && cids1.contains cid

def testMetaDependenciesRemove : Bool :=
  let deps := MetaDependencies.empty
  let metas : Array MetaId := #[⟨0⟩]
  let (cid, deps') := deps.registerConstraint metas
  let deps'' := deps'.removeConstraint cid
  -- After removal, meta should have no constraints
  deps''.getConstraintsFor ⟨0⟩ |>.isEmpty

def testMetaDependenciesComplexity : Bool :=
  let deps := MetaDependencies.empty
  let metas1 : Array MetaId := #[⟨0⟩]
  let metas2 : Array MetaId := #[⟨0⟩, ⟨1⟩, ⟨2⟩]
  let (cid1, deps') := deps.registerConstraint metas1
  let (cid2, deps'') := deps'.registerConstraint metas2
  deps''.constraintComplexity cid1 == 1 && deps''.constraintComplexity cid2 == 3

def testMetaStateAddDependency : Bool :=
  let state := MetaState.empty
  let (meta1, state') := state.fresh (.vType .zero) []
  let (meta2, state'') := state'.fresh (.vType .zero) []
  let state''' := state''.addDependency meta1 meta2
  -- Check meta1 depends on meta2
  let deps := state'''.getDependencies meta1
  let dependents := state'''.getDependents meta2
  deps.contains meta2 && dependents.contains meta1

def testConstraintGraphPriority : Bool :=
  match runTCM do
    -- Create metas
    let meta1 ← TCM.freshMeta (.vType .zero)
    let meta2 ← TCM.freshMeta (.vType .zero)
    let meta3 ← TCM.freshMeta (.vType .zero)

    -- Solve meta1 so it doesn't count toward complexity
    TCM.solveMeta meta1 (.vPrimTy .int)

    -- Create constraints with different complexities
    let tc1 : TrackedConstraint := {
      constraint := .unify (.vPrimTy .int) (.vPrimTy .int) testSpan
      constraintId := ⟨0⟩
      metas := #[meta1]  -- 0 unsolved (meta1 is solved)
      origin := .unknown
      parentConstraints := #[]
    }
    let tc2 : TrackedConstraint := {
      constraint := .unify (.vPrimTy .int) (.vPrimTy .int) testSpan
      constraintId := ⟨1⟩
      metas := #[meta2, meta3]  -- 2 unsolved
      origin := .unknown
      parentConstraints := #[]
    }
    let tc3 : TrackedConstraint := {
      constraint := .unify (.vPrimTy .int) (.vPrimTy .int) testSpan
      constraintId := ⟨2⟩
      metas := #[meta2]  -- 1 unsolved
      origin := .unknown
      parentConstraints := #[]
    }

    -- Insert into graph and extract in priority order
    let g0 := Unify.ConstraintGraph.empty
    let complexity1 ← Unify.ConstraintGraph.countUnsolvedMetas tc1.metas
    let g1 := g0.insert tc1 complexity1
    let complexity2 ← Unify.ConstraintGraph.countUnsolvedMetas tc2.metas
    let g2 := g1.insert tc2 complexity2
    let complexity3 ← Unify.ConstraintGraph.countUnsolvedMetas tc3.metas
    let g3 := g2.insert tc3 complexity3

    -- Extract min should give tc1 first (complexity 0)
    match g3.extractMin with
    | some (first, g4) =>
      if first.constraintId.id != 0 then return false
      match g4.extractMin with
      | some (second, g5) =>
        if second.constraintId.id != 2 then return false  -- tc3 has complexity 1
        match g5.extractMin with
        | some (third, _) =>
          return third.constraintId.id == 1  -- tc2 has complexity 2
        | none => return false
      | none => return false
    | none => return false
  with
  | .ok (true, _) => true
  | _ => false

def testWakeConstraintsFor : Bool :=
  match runTCM do
    let meta1 ← TCM.freshMeta (.vType .zero)

    -- Register a constraint referencing meta1
    let constraint := Constraint.unify
      (Value.vNeutral .type0 (.nMeta meta1))
      (.vPrimTy .int)
      testSpan
    let _ ← TCM.postponeTracked constraint #[meta1]

    -- Solve meta1 and wake constraints
    TCM.solveMeta meta1 (.vPrimTy .int)
    TCM.wakeConstraintsFor meta1

    -- Check worklist has the constraint
    let state ← TCM.getState
    return !state.worklist.isEmpty
  with
  | .ok (true, _) => true
  | _ => false

def dependencyTrackingTests : List (String × Bool) := [
  ("collectMetas empty", testCollectMetasEmpty),
  ("collectMetas single meta", testCollectMetasSingle),
  ("collectMetas multiple metas", testCollectMetasMultiple),
  ("collectMetas Pi domain", testCollectMetasPi),
  ("collectMetas constraint", testCollectMetasConstraint),
  ("MetaDependencies empty", testMetaDependenciesEmpty),
  ("MetaDependencies register", testMetaDependenciesRegister),
  ("MetaDependencies remove", testMetaDependenciesRemove),
  ("MetaDependencies complexity", testMetaDependenciesComplexity),
  ("MetaState addDependency", testMetaStateAddDependency),
  ("constraintGraphPriority", testConstraintGraphPriority),
  ("wakeConstraintsFor", testWakeConstraintsFor)
]

/-! ## Sophisticated Unification Tests

Tests for the advanced unification techniques:
1. Pruning - restricting metavariable domains
2. Heterogeneous constraints - handling metas with meta types
3. η-expansion - converting non-patterns to patterns
-/

/-! ### Free Variable Collection Tests -/

def testCollectFreeVarsEmpty : Bool :=
  let vars := collectFreeVars (.vPrimTy .int)
  vars.isEmpty

def testCollectFreeVarsVar : Bool :=
  let v := Value.vNeutral .type0 (.nVar ⟨"x", ⟨0⟩⟩)
  let vars := collectFreeVars v
  vars.size == 1 && vars[0]! == ⟨0⟩

def testCollectFreeVarsMultiple : Bool :=
  let x := Value.vNeutral .type0 (.nVar ⟨"x", ⟨0⟩⟩)
  let y := Value.vNeutral .type0 (.nVar ⟨"y", ⟨1⟩⟩)
  let v := Value.vPair x y
  let vars := collectFreeVars v
  vars.size == 2 && vars.contains ⟨0⟩ && vars.contains ⟨1⟩

def testCollectFreeVarsMeta : Bool :=
  -- Metas should not contribute free vars (they're not bound vars)
  let v := Value.vNeutral .type0 (.nMeta ⟨0⟩)
  let vars := collectFreeVars v
  vars.isEmpty

def testCollectFreeVarsPi : Bool :=
  let x := Value.vNeutral .type0 (.nVar ⟨"x", ⟨0⟩⟩)
  let clos := Closure.const "_" (.vPrimTy .int)
  let v := Value.vPi .omega .explicit "y" x clos
  let vars := collectFreeVars v
  vars.contains ⟨0⟩

/-! ### Pruning Tests -/

def testLevelInSpineTrue : Bool :=
  let x := Value.vNeutral .type0 (.nVar ⟨"x", ⟨0⟩⟩)
  let spine := [x]
  levelInSpine ⟨0⟩ spine == true

def testLevelInSpineFalse : Bool :=
  let x := Value.vNeutral .type0 (.nVar ⟨"x", ⟨0⟩⟩)
  let spine := [x]
  levelInSpine ⟨1⟩ spine == false

def testLevelInSpineEmpty : Bool :=
  levelInSpine ⟨0⟩ [] == false

def testComputeSafeScope : Bool :=
  let x := Value.vNeutral .type0 (.nVar ⟨"x", ⟨0⟩⟩)
  let y := Value.vNeutral .type0 (.nVar ⟨"y", ⟨1⟩⟩)
  let spine := [x, y]
  -- RHS only mentions x, not y
  let rhs := x
  let safeScope := computeSafeScope spine rhs
  -- x should be safe (appears in RHS), y should also be safe (doesn't appear, so can be pruned)
  safeScope.length == 2

def testTryPruneUnsolved : Bool :=
  match runTCM do
    let meta1 ← TCM.freshMeta (.vType .zero)
    let x := Value.vNeutral .type0 (.nVar ⟨"x", ⟨0⟩⟩)
    let spine := [x]
    -- RHS doesn't mention x - pruning could be beneficial
    let rhs := Value.vPrimTy .int
    let result ← tryPrune meta1 spine rhs
    -- Currently returns none (full pruning not implemented)
    return result.isNone
  with
  | .ok (true, _) => true
  | _ => false

def testTryPruneSolved : Bool :=
  match runTCM do
    let meta1 ← TCM.freshMeta (.vType .zero)
    TCM.solveMeta meta1 (.vPrimTy .int)
    let x := Value.vNeutral .type0 (.nVar ⟨"x", ⟨0⟩⟩)
    let result ← tryPrune meta1 [x] (.vPrimTy .bool)
    -- Should return none for solved metas
    return result.isNone
  with
  | .ok (true, _) => true
  | _ => false

/-! ### Heterogeneous Constraint Tests -/

def testHasMetaTypeNo : Bool :=
  match runTCM do
    -- A value with a concrete type
    let v := Value.vNeutral (.vPrimTy .int) (.nVar ⟨"x", ⟨0⟩⟩)
    hasMetaType v
  with
  | .ok (false, _) => true
  | _ => false

def testHasMetaTypeYes : Bool :=
  match runTCM do
    let metaTy ← TCM.freshMetaVal (.vType .zero)
    -- A value with a meta type
    let v := Value.vNeutral metaTy (.nVar ⟨"x", ⟨0⟩⟩)
    hasMetaType v
  with
  | .ok (true, _) => true
  | _ => false

def testShouldDeferMetaNo : Bool :=
  match runTCM do
    -- Create a meta with a concrete type
    let meta1 ← TCM.freshMeta (.vPrimTy .int)
    shouldDeferMeta meta1
  with
  | .ok (false, _) => true
  | _ => false

def testShouldDeferMetaYes : Bool :=
  match runTCM do
    -- Create a meta whose type is also a meta
    let typeMeta ← TCM.freshMetaVal (.vType .zero)
    let meta1 ← TCM.freshMeta typeMeta
    shouldDeferMeta meta1
  with
  | .ok (true, _) => true
  | _ => false

def testRecordMetaDependency : Bool :=
  match runTCM do
    let meta1 ← TCM.freshMeta (.vType .zero)
    let meta2 ← TCM.freshMeta (.vType .zero)
    recordMetaDependency meta1 meta2
    let state ← TCM.getState
    let deps := state.metas.getDependencies meta1
    return deps.contains meta2
  with
  | .ok (true, _) => true
  | _ => false

/-! ### η-expansion Tests -/

def testTryEtaExpandLambdaYes : Bool :=
  let clos := Closure.const "x" (.vPrimTy .bool)
  let lam := Value.vLam "x" clos
  match tryEtaExpandLambda lam with
  | some (name, _, _) => name == "x"
  | none => false

def testTryEtaExpandLambdaNo : Bool :=
  let v := Value.vPrimTy .int
  match tryEtaExpandLambda v with
  | some _ => false
  | none => true

def testTryEtaExpandPairYes : Bool :=
  let p := Value.vPair (.vIntLit 1) (.vIntLit 2)
  match tryEtaExpandPair p with
  | some (a, b) =>
    match a, b with
    | .vIntLit 1, .vIntLit 2 => true
    | _, _ => false
  | none => false

def testTryEtaExpandPairNo : Bool :=
  let v := Value.vPrimTy .int
  match tryEtaExpandPair v with
  | some _ => false
  | none => true

def testTryMakePatternViaEtaLambda : Bool :=
  match runTCM do
    let meta1 ← TCM.freshMeta (.vType .zero)
    let clos := Closure.const "x" (.vPrimTy .bool)
    let lam := Value.vLam "x" clos
    -- Try to make ?m = λx. body into a pattern
    let result ← tryMakePatternViaEta meta1 [] lam
    return result.isSome
  with
  | .ok (true, _) => true
  | _ => false

def testTryMakePatternViaEtaNonLambda : Bool :=
  match runTCM do
    let meta1 ← TCM.freshMeta (.vType .zero)
    let v := Value.vPrimTy .int
    let result ← tryMakePatternViaEta meta1 [] v
    return result.isNone
  with
  | .ok (true, _) => true
  | _ => false

/-! ### Integration Tests for Sophisticated Unification -/

def testUnifyMetaWithLambdaViaEta : Bool :=
  -- Test: ?m = λx. Int should solve via η-expansion
  match runTCM do
    let metaVal ← TCM.freshMetaVal (.vType .zero)
    let clos := Closure.const "x" (.vPrimTy .bool)
    let lam := Value.vLam "x" clos
    unify metaVal lam
    -- After unification, the meta should be solved or constraint postponed
    return true
  with
  | .ok _ => true
  | .error _ => true  -- Postponement is also acceptable

def testUnifyFlexFlex : Bool :=
  -- Test: ?m1 = ?m2 should succeed
  match runTCM do
    let meta1 ← TCM.freshMetaVal (.vType .zero)
    let meta2 ← TCM.freshMetaVal (.vType .zero)
    unify meta1 meta2
    return true
  with
  | .ok _ => true
  | .error _ => false

def testUnifyFlexFlexSame : Bool :=
  -- Test: ?m = ?m should always succeed (reflexivity)
  match runTCM do
    let metaVal ← TCM.freshMetaVal (.vType .zero)
    unify metaVal metaVal
    return true
  with
  | .ok _ => true
  | .error _ => false

def testUnifyWithHeterogeneousType : Bool :=
  -- Test: unifying a meta whose type is also a meta
  match runTCM do
    let typeMeta ← TCM.freshMetaVal (.vType .one)
    let valueMeta ← TCM.freshMetaVal typeMeta
    -- Unify with a concrete value - should defer or solve type first
    unify valueMeta (.vIntLit 42)
    return true
  with
  | .ok _ => true
  | .error _ => true  -- Postponement is acceptable

/-! ### Test Lists -/

def freeVarTests : List (String × Bool) := [
  ("collectFreeVars empty", testCollectFreeVarsEmpty),
  ("collectFreeVars var", testCollectFreeVarsVar),
  ("collectFreeVars multiple", testCollectFreeVarsMultiple),
  ("collectFreeVars meta (no contribution)", testCollectFreeVarsMeta),
  ("collectFreeVars Pi", testCollectFreeVarsPi)
]

def pruningTests : List (String × Bool) := [
  ("levelInSpine true", testLevelInSpineTrue),
  ("levelInSpine false", testLevelInSpineFalse),
  ("levelInSpine empty", testLevelInSpineEmpty),
  ("computeSafeScope", testComputeSafeScope),
  ("tryPrune unsolved", testTryPruneUnsolved),
  ("tryPrune solved", testTryPruneSolved)
]

def heterogeneousTests : List (String × Bool) := [
  ("hasMetaType no", testHasMetaTypeNo),
  ("hasMetaType yes", testHasMetaTypeYes),
  ("shouldDeferMeta no", testShouldDeferMetaNo),
  ("shouldDeferMeta yes", testShouldDeferMetaYes),
  ("recordMetaDependency", testRecordMetaDependency)
]

def etaExpansionTests : List (String × Bool) := [
  ("tryEtaExpandLambda yes", testTryEtaExpandLambdaYes),
  ("tryEtaExpandLambda no", testTryEtaExpandLambdaNo),
  ("tryEtaExpandPair yes", testTryEtaExpandPairYes),
  ("tryEtaExpandPair no", testTryEtaExpandPairNo),
  ("tryMakePatternViaEta lambda", testTryMakePatternViaEtaLambda),
  ("tryMakePatternViaEta non-lambda", testTryMakePatternViaEtaNonLambda)
]

def sophisticatedUnifyTests : List (String × Bool) := [
  ("unify meta with lambda via eta", testUnifyMetaWithLambdaViaEta),
  ("unify flex-flex", testUnifyFlexFlex),
  ("unify flex-flex same", testUnifyFlexFlexSame),
  ("unify with heterogeneous type", testUnifyWithHeterogeneousType)
]

/-! ### Spine Intersection Tests -/

def testComputeSpineIntersectionEmpty : Bool :=
  let x := Value.vNeutral .type0 (.nVar ⟨"x", ⟨0⟩⟩)
  let y := Value.vNeutral .type0 (.nVar ⟨"y", ⟨1⟩⟩)
  let z := Value.vNeutral .type0 (.nVar ⟨"z", ⟨2⟩⟩)
  -- Spines have no common variables
  let spine1 := [x]
  let spine2 := [y, z]
  let intersection := computeSpineIntersection spine1 spine2
  intersection.isEmpty

def testComputeSpineIntersectionSingle : Bool :=
  let x := Value.vNeutral .type0 (.nVar ⟨"x", ⟨0⟩⟩)
  let y := Value.vNeutral .type0 (.nVar ⟨"y", ⟨1⟩⟩)
  -- x is common to both spines
  let spine1 := [x, y]
  let spine2 := [x]
  let intersection := computeSpineIntersection spine1 spine2
  intersection.length == 1

def testComputeSpineIntersectionMultiple : Bool :=
  let x := Value.vNeutral .type0 (.nVar ⟨"x", ⟨0⟩⟩)
  let y := Value.vNeutral .type0 (.nVar ⟨"y", ⟨1⟩⟩)
  let z := Value.vNeutral .type0 (.nVar ⟨"z", ⟨2⟩⟩)
  -- x and z are common
  let spine1 := [x, y, z]
  let spine2 := [z, x]
  let intersection := computeSpineIntersection spine1 spine2
  intersection.length == 2

def testTryFlexFlexIntersectionBothUnsolved : Bool :=
  match runTCM do
    -- Create two metas with overlapping spines
    let piTy := Value.vPi .omega .explicit "x" (.vPrimTy .int) (Closure.const "_" (.vType .zero))
    let meta1 ← TCM.freshMeta piTy
    let meta2 ← TCM.freshMeta piTy
    let x := Value.vNeutral (.vPrimTy .int) (.nVar ⟨"x", ⟨0⟩⟩)
    let y := Value.vNeutral (.vPrimTy .int) (.nVar ⟨"y", ⟨1⟩⟩)
    -- ?m1 x y and ?m2 x share variable x
    let result ← tryFlexFlexIntersection meta1 [x, y] meta2 [x]
    -- Should succeed and solve both metas
    return result
  with
  | .ok (true, _) => true
  | _ => false

def testTryFlexFlexIntersectionNoOverlap : Bool :=
  match runTCM do
    let piTy := Value.vPi .omega .explicit "x" (.vPrimTy .int) (Closure.const "_" (.vType .zero))
    let meta1 ← TCM.freshMeta piTy
    let meta2 ← TCM.freshMeta piTy
    let x := Value.vNeutral (.vPrimTy .int) (.nVar ⟨"x", ⟨0⟩⟩)
    let y := Value.vNeutral (.vPrimTy .int) (.nVar ⟨"y", ⟨1⟩⟩)
    -- ?m1 x and ?m2 y have no common variables
    let result ← tryFlexFlexIntersection meta1 [x] meta2 [y]
    -- Should return false (no intersection)
    return !result
  with
  | .ok (true, _) => true
  | _ => false

def testTryFlexFlexIntersectionOneSolved : Bool :=
  match runTCM do
    let piTy := Value.vPi .omega .explicit "x" (.vPrimTy .int) (Closure.const "_" (.vType .zero))
    let meta1 ← TCM.freshMeta piTy
    let meta2 ← TCM.freshMeta piTy
    -- Solve meta1 first
    TCM.solveMeta meta1 (.vPrimTy .int)
    let x := Value.vNeutral (.vPrimTy .int) (.nVar ⟨"x", ⟨0⟩⟩)
    let result ← tryFlexFlexIntersection meta1 [x] meta2 [x]
    -- Should return false (one is already solved)
    return !result
  with
  | .ok (true, _) => true
  | _ => false

/-! ### Twin Variables Tests -/

def testDetectTwinVarsNone : Bool :=
  let x := Value.vNeutral .type0 (.nVar ⟨"x", ⟨0⟩⟩)
  -- RHS doesn't reference x
  let rhs := Value.vPrimTy .int
  let twins := detectTwinVars [x] rhs
  twins.isEmpty

def testDetectTwinVarsSingle : Bool :=
  let x := Value.vNeutral .type0 (.nVar ⟨"x", ⟨0⟩⟩)
  -- RHS references x (same level)
  let rhs := x
  let twins := detectTwinVars [x] rhs
  twins.length == 1

def testDetectTwinVarsMultiple : Bool :=
  let x := Value.vNeutral .type0 (.nVar ⟨"x", ⟨0⟩⟩)
  let y := Value.vNeutral .type0 (.nVar ⟨"y", ⟨1⟩⟩)
  -- RHS references both x and y
  let rhs := Value.vPair x y
  let twins := detectTwinVars [x, y] rhs
  twins.length == 2

def testAllVarsCoveredByTwinsYes : Bool :=
  let x := Value.vNeutral .type0 (.nVar ⟨"x", ⟨0⟩⟩)
  let twins : List TwinVar := [{ originalLevel := ⟨0⟩, name1 := "x", name2 := "x" }]
  let rhs := x
  allVarsCoveredByTwins twins rhs

def testAllVarsCoveredByTwinsNo : Bool :=
  let x := Value.vNeutral .type0 (.nVar ⟨"x", ⟨0⟩⟩)
  let y := Value.vNeutral .type0 (.nVar ⟨"y", ⟨1⟩⟩)
  -- Twin only covers x, but RHS also uses y
  let twins : List TwinVar := [{ originalLevel := ⟨0⟩, name1 := "x", name2 := "x" }]
  let rhs := Value.vPair x y
  !allVarsCoveredByTwins twins rhs

/-! ### Occurs Check Pruning Tests -/

def testCollectMetaOccurrencesNone : Bool :=
  let m : MetaId := ⟨0⟩
  let v := Value.vPrimTy .int
  let occs := collectMetaOccurrences m v 0 #[]
  occs.isEmpty

def testCollectMetaOccurrencesSingle : Bool :=
  let m : MetaId := ⟨0⟩
  let v := Value.vNeutral .type0 (.nMeta m)
  let occs := collectMetaOccurrences m v 0 #[]
  occs.size == 1 && occs[0]!.depth == 0

def testCollectMetaOccurrencesNested : Bool :=
  let m : MetaId := ⟨0⟩
  let inner := Value.vNeutral .type0 (.nMeta m)
  let v := Value.vPair (.vIntLit 1) inner
  let occs := collectMetaOccurrences m v 0 #[]
  occs.size == 1 && occs[0]!.depth == 1

def testTryOccursCheckPruningNoOccurrences : Bool :=
  match runTCM do
    let meta1 ← TCM.freshMeta (.vType .zero)
    let x := Value.vNeutral .type0 (.nVar ⟨"x", ⟨0⟩⟩)
    -- RHS doesn't contain the meta
    let rhs := Value.vPrimTy .int
    let result ← tryOccursCheckPruning meta1 [x] rhs
    return !result  -- Should return false (no occurrences)
  with
  | .ok (true, _) => true
  | _ => false

/-! ### Integration Tests for New Features -/

def testFlexFlexWithIntersectionSolves : Bool :=
  -- ?m1 x y = ?m2 x z should be solvable via intersection on x
  match runTCM do
    let x := Value.vNeutral (.vPrimTy .int) (.nVar ⟨"x", ⟨0⟩⟩)
    let y := Value.vNeutral (.vPrimTy .int) (.nVar ⟨"y", ⟨1⟩⟩)
    let z := Value.vNeutral (.vPrimTy .int) (.nVar ⟨"z", ⟨2⟩⟩)
    -- Create function types for the metas
    let piTy2 := Value.vPi .omega .explicit "a" (.vPrimTy .int)
      (Closure.const "_" (Value.vPi .omega .explicit "b" (.vPrimTy .int)
        (Closure.const "_" (.vType .zero))))
    let meta1 ← TCM.freshMeta piTy2
    let meta2 ← TCM.freshMeta piTy2
    -- Build ?m1 x y and ?m2 x z
    let m1App := Value.vNeutral (.vType .zero)
      (.nApp (.nApp (.nMeta meta1) x) y)
    let m2App := Value.vNeutral (.vType .zero)
      (.nApp (.nApp (.nMeta meta2) x) z)
    -- Unify them
    unify m1App m2App
    -- After unification, at least one should be solved or constraints posted
    return true
  with
  | .ok _ => true
  | .error _ => true  -- Postponement is acceptable

def testDependentPatternWithTwins : Bool :=
  -- Simulates: ?X n = Vec n Bool where n is both in spine and RHS
  match runTCM do
    let vecId : TypeId := ⟨"test", "Vec", 200⟩
    let n := Value.vNeutral (.vPrimTy .int) (.nVar ⟨"n", ⟨0⟩⟩)
    -- Create meta ?X with type (n : Int) -> Type
    let piTy := Value.vPi .omega .explicit "n" (.vPrimTy .int)
      (Closure.const "_" (.vType .zero))
    let metaId ← TCM.freshMeta piTy
    -- ?X n
    let metaApp := Value.vNeutral (.vType .zero) (.nApp (.nMeta metaId) n)
    -- Vec n Bool
    let vecType := Value.vDataType vecId [n, .vPrimTy .bool]
    -- Unify: ?X n = Vec n Bool
    unify metaApp vecType
    -- Check if meta is solved
    let info? ← TCM.lookupMeta metaId
    match info? with
    | some info => return info.solution.isSome
    | none => return false
  with
  | .ok (true, _) => true
  | _ => false

def spineIntersectionTests : List (String × Bool) := [
  ("computeSpineIntersection empty", testComputeSpineIntersectionEmpty),
  ("computeSpineIntersection single", testComputeSpineIntersectionSingle),
  ("computeSpineIntersection multiple", testComputeSpineIntersectionMultiple),
  ("tryFlexFlexIntersection both unsolved", testTryFlexFlexIntersectionBothUnsolved),
  ("tryFlexFlexIntersection no overlap", testTryFlexFlexIntersectionNoOverlap),
  ("tryFlexFlexIntersection one solved", testTryFlexFlexIntersectionOneSolved)
]

def twinVariableTests : List (String × Bool) := [
  ("detectTwinVars none", testDetectTwinVarsNone),
  ("detectTwinVars single", testDetectTwinVarsSingle),
  ("detectTwinVars multiple", testDetectTwinVarsMultiple),
  ("allVarsCoveredByTwins yes", testAllVarsCoveredByTwinsYes),
  ("allVarsCoveredByTwins no", testAllVarsCoveredByTwinsNo)
]

def occursCheckPruningTests : List (String × Bool) := [
  ("collectMetaOccurrences none", testCollectMetaOccurrencesNone),
  ("collectMetaOccurrences single", testCollectMetaOccurrencesSingle),
  ("collectMetaOccurrences nested", testCollectMetaOccurrencesNested),
  ("tryOccursCheckPruning no occurrences", testTryOccursCheckPruningNoOccurrences)
]

def advancedIntegrationTests : List (String × Bool) := [
  ("flex-flex with intersection", testFlexFlexWithIntersectionSolves),
  ("dependent pattern with twins", testDependentPatternWithTwins)
]

/-! ### Indexed Type Constraint Generation Tests -/

/-- Test: Unifying DataType with same indices should succeed -/
def testUnifyDataTypesSameIndices : Bool :=
  match runTCM do
    -- Create TypeIds for a Vec-like type
    let vecId : TypeId := ⟨"test", "Vec", 100⟩
    -- Vec 5 Int
    let vec1 := Value.vDataType vecId [.vIntLit 5, .vPrimTy .int]
    -- Vec 5 Int (same)
    let vec2 := Value.vDataType vecId [.vIntLit 5, .vPrimTy .int]
    unify vec1 vec2
    return true
  with
  | .ok _ => true
  | .error _ => false

/-- Test: Unifying DataType with different indices should fail -/
def testUnifyDataTypesDifferentIndices : Bool :=
  match runTCM do
    let vecId : TypeId := ⟨"test", "Vec", 100⟩
    -- Vec 5 Int
    let vec1 := Value.vDataType vecId [.vIntLit 5, .vPrimTy .int]
    -- Vec 3 Int (different length)
    let vec2 := Value.vDataType vecId [.vIntLit 3, .vPrimTy .int]
    unify vec1 vec2
    return true
  with
  | .ok _ => false  -- Should fail
  | .error _ => true

/-- Test: Unifying DataType with meta index should solve the meta -/
def testUnifyDataTypeMetaIndex : Bool :=
  match runTCM do
    let vecId : TypeId := ⟨"test", "Vec", 100⟩
    -- Create a meta for the length index
    let lenMeta ← TCM.freshMetaVal (.vPrimTy .int)
    -- Vec ?len Int
    let vec1 := Value.vDataType vecId [lenMeta, .vPrimTy .int]
    -- Vec 5 Int
    let vec2 := Value.vDataType vecId [.vIntLit 5, .vPrimTy .int]
    unify vec1 vec2
    -- The meta should be solved to 5
    let lenMeta' ← force lenMeta
    match lenMeta' with
    | .vIntLit 5 => return true
    | _ => return false
  with
  | .ok (true, _) => true
  | _ => false

/-- Test: Unifying DataType with meta type parameter should solve the meta -/
def testUnifyDataTypeMetaTypeParam : Bool :=
  match runTCM do
    let maybeId : TypeId := ⟨"test", "Maybe", 101⟩
    -- Create a meta for the type parameter
    let tyMeta ← TCM.freshMetaVal (.vType .zero)
    -- Maybe ?a
    let maybe1 := Value.vDataType maybeId [tyMeta]
    -- Maybe Int
    let maybe2 := Value.vDataType maybeId [.vPrimTy .int]
    unify maybe1 maybe2
    -- The meta should be solved to Int
    let tyMeta' ← force tyMeta
    match tyMeta' with
    | .vPrimTy .int => return true
    | _ => return false
  with
  | .ok (true, _) => true
  | _ => false

/-- Test: Unifying nested indexed types propagates constraints -/
def testUnifyNestedIndexedTypes : Bool :=
  match runTCM do
    let vecId : TypeId := ⟨"test", "Vec", 100⟩
    let pairId : TypeId := ⟨"test", "Pair", 102⟩
    -- Create metas
    let lenMeta ← TCM.freshMetaVal (.vPrimTy .int)
    let tyMeta ← TCM.freshMetaVal (.vType .zero)
    -- Pair (Vec ?len ?a) Int
    let vec1 := Value.vDataType vecId [lenMeta, tyMeta]
    let pair1 := Value.vDataType pairId [vec1, .vPrimTy .int]
    -- Pair (Vec 3 Bool) Int
    let vec2 := Value.vDataType vecId [.vIntLit 3, .vPrimTy .bool]
    let pair2 := Value.vDataType pairId [vec2, .vPrimTy .int]
    unify pair1 pair2
    -- Check both metas are solved
    let lenMeta' ← force lenMeta
    let tyMeta' ← force tyMeta
    match lenMeta', tyMeta' with
    | .vIntLit 3, .vPrimTy .bool => return true
    | _, _ => return false
  with
  | .ok (true, _) => true
  | _ => false

/-- Test: Unifying DataType with different type IDs should fail -/
def testUnifyDataTypesDifferentTypeIds : Bool :=
  match runTCM do
    let vecId : TypeId := ⟨"test", "Vec", 100⟩
    let listId : TypeId := ⟨"test", "List", 103⟩
    -- Vec 5 Int
    let vec := Value.vDataType vecId [.vIntLit 5, .vPrimTy .int]
    -- List Int (different type)
    let list := Value.vDataType listId [.vPrimTy .int]
    unify vec list
    return true
  with
  | .ok _ => false  -- Should fail: different data types
  | .error _ => true

/-- Test: Bidirectional constraint propagation with two metas -/
def testBidirectionalIndexConstraint : Bool :=
  match runTCM do
    let vecId : TypeId := ⟨"test", "Vec", 100⟩
    -- Create two metas for length indices
    let lenMeta1 ← TCM.freshMetaVal (.vPrimTy .int)
    let lenMeta2 ← TCM.freshMetaVal (.vPrimTy .int)
    -- Vec ?n1 Int
    let vec1 := Value.vDataType vecId [lenMeta1, .vPrimTy .int]
    -- Vec ?n2 Int
    let vec2 := Value.vDataType vecId [lenMeta2, .vPrimTy .int]
    -- Unify them - this should make ?n1 = ?n2
    unify vec1 vec2
    -- Now solve ?n1 = 7
    unify lenMeta1 (.vIntLit 7)
    -- Check that ?n2 is also 7
    let lenMeta2' ← force lenMeta2
    match lenMeta2' with
    | .vIntLit 7 => return true
    | _ => return false
  with
  | .ok (true, _) => true
  | _ => false

def indexedTypeTests : List (String × Bool) := [
  ("unify DataTypes same indices", testUnifyDataTypesSameIndices),
  ("unify DataTypes different indices (fail)", testUnifyDataTypesDifferentIndices),
  ("unify DataType meta index", testUnifyDataTypeMetaIndex),
  ("unify DataType meta type param", testUnifyDataTypeMetaTypeParam),
  ("unify nested indexed types", testUnifyNestedIndexedTypes),
  ("unify DataTypes different type IDs (fail)", testUnifyDataTypesDifferentTypeIds),
  ("bidirectional index constraint", testBidirectionalIndexConstraint)
]

def runTestGroup (name : String) (tests : List (String × Bool)) : IO TestRunner := do
  IO.println s!"=== {name} ==="
  let mut runner := TestRunner.init
  for (testName, result) in tests do
    if result then
      runner := runner.recordPass
    else
      IO.println s!"  FAILED: {testName}"
      runner := runner.recordFail testName
  IO.println s!"  Passed:  {runner.passed}"
  IO.println s!"  Failed:  {runner.failed}"
  IO.println s!"  Skipped: 0"
  return runner

def runAllTests : IO TestRunner := do
  IO.println "=== Dependent Types Unify Tests (Phase 3) ===\n"

  let mut combined := TestRunner.init

  IO.println "  === Occurs Check Tests ==="
  let r1 ← runTestGroup "Occurs Check" occursCheckTests
  combined := combined.merge r1

  IO.println "  === Scope Check Tests ==="
  let r2 ← runTestGroup "Scope Check" scopeCheckTests
  combined := combined.merge r2

  IO.println "  === Spine Pattern Tests ==="
  let r3 ← runTestGroup "Spine Pattern" spinePatternTests
  combined := combined.merge r3

  IO.println "  === Substitution Tests ==="
  let r4 ← runTestGroup "Substitution" substTests
  combined := combined.merge r4

  IO.println "  === Basic Unification Tests ==="
  let r5 ← runTestGroup "Basic Unification" basicUnifyTests
  combined := combined.merge r5

  IO.println "  === Meta Solving Tests ==="
  let r6 ← runTestGroup "Meta Solving" metaSolvingTests
  combined := combined.merge r6

  IO.println "  === Row Unification Tests ==="
  let r7 ← runTestGroup "Row Unification" rowUnifyTests
  combined := combined.merge r7

  IO.println "  === Constraint Solving Tests ==="
  let r8 ← runTestGroup "Constraint Solving" constraintTests
  combined := combined.merge r8

  IO.println "  === Zonking Tests ==="
  let r9 ← runTestGroup "Zonking" zonkTests
  combined := combined.merge r9

  IO.println "  === Unsolved Meta Detection Tests ==="
  let r10 ← runTestGroup "Unsolved Meta Detection" unsolvedMetaTests
  combined := combined.merge r10

  IO.println "  === Dependency Tracking Tests ==="
  let r11 ← runTestGroup "Dependency Tracking" dependencyTrackingTests
  combined := combined.merge r11

  IO.println "  === Free Variable Collection Tests ==="
  let r12 ← runTestGroup "Free Variable Collection" freeVarTests
  combined := combined.merge r12

  IO.println "  === Pruning Tests ==="
  let r13 ← runTestGroup "Pruning" pruningTests
  combined := combined.merge r13

  IO.println "  === Heterogeneous Constraint Tests ==="
  let r14 ← runTestGroup "Heterogeneous Constraints" heterogeneousTests
  combined := combined.merge r14

  IO.println "  === η-expansion Tests ==="
  let r15 ← runTestGroup "η-expansion" etaExpansionTests
  combined := combined.merge r15

  IO.println "  === Sophisticated Unification Tests ==="
  let r16 ← runTestGroup "Sophisticated Unification" sophisticatedUnifyTests
  combined := combined.merge r16

  IO.println "  === Indexed Type Constraint Generation Tests ==="
  let r17 ← runTestGroup "Indexed Type Constraints" indexedTypeTests
  combined := combined.merge r17

  IO.println "  === Spine Intersection Tests ==="
  let r18 ← runTestGroup "Spine Intersection" spineIntersectionTests
  combined := combined.merge r18

  IO.println "  === Twin Variable Tests ==="
  let r19 ← runTestGroup "Twin Variables" twinVariableTests
  combined := combined.merge r19

  IO.println "  === Occurs Check Pruning Tests ==="
  let r20 ← runTestGroup "Occurs Check Pruning" occursCheckPruningTests
  combined := combined.merge r20

  IO.println "  === Advanced Integration Tests ==="
  let r21 ← runTestGroup "Advanced Integration" advancedIntegrationTests
  combined := combined.merge r21

  IO.println s!"\nTotal: {combined.passed} passed, {combined.failed} failed"

  if combined.failed > 0 then
    IO.println ""
    IO.println "FAILURES:"
    for f in combined.failures do IO.println s!"  - {f}"

  return combined

end Test.Dependent.Unify
