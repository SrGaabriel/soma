import Soma.Dependent.Monad
import Soma.Dependent.Convert
import Soma.Dependent.Unify
import Soma.Dependent.Instance
import Soma.Dependent.Level

namespace Soma.Dependent

open Soma.Core
open Soma.Syntax (Span)
open Soma.Dependent.Unify (SolveResult ConstraintGraph)

/-- Structured result for a solver boundary -/
structure SolveReport where
  mode : String
  remaining : Array TrackedConstraint
  deriving Inhabited

namespace SolveReport

/-- Explicitly accept constraints that are still blocked at a soft boundary -/
def allowPostponed (_r : SolveReport) : TCM Unit :=
  pure ()

end SolveReport

/-- Collect every UNSOLVED metavariable referenced inside a value -/
private def unsolvedMetasIn (v : Value) : TCM (Array MetaId) := do
  let mut out : Array MetaId := #[]
  let mut seen : Std.HashSet Nat := {}
  for m in Value.collectMetas v do
    if seen.contains m.id then continue
    seen := seen.insert m.id
    if !(← TCM.isMetaSolved m) then out := out.push m
  return out

/-- Build the set of metas an instance-resolution constraint should block on -/
private def blockedMetasForInstance (metaId : MetaId) (args : Array Value)
    : TCM (Array MetaId) := do
  let mut out : Array MetaId := #[metaId]
  let mut seen : Std.HashSet Nat := { metaId.id }
  for a in args do
    for m in (← unsolvedMetasIn a) do
      if !seen.contains m.id then
        seen := seen.insert m.id
        out := out.push m
  return out

/-- Try to solve a single instance-resolution constraint -/
private def trySolveResolveInstance
    (metaId : MetaId) (classId : Unique) (args : Array Value) (span : Span)
    : TCM SolveResult := do
  if (← TCM.isMetaSolved metaId) then return .solved
  let forcedArgs ← args.mapM deepForceValue
  let deps ← blockedMetasForInstance metaId forcedArgs
  if deps.size > 1 then return .blocked deps #[]
  match ← resolveInstance classId forcedArgs with
  | .found value _ =>
    TCM.solveMeta metaId value (callerTag := "Solver.resolveInstance")
    return .solved
  | .notFound classId args _reason =>
    return .failed (.noInstance classId args span #[] #[])
  | .cycle classId _args =>
    return .failed (.instanceCycle classId span #[])
  | .depthExceeded classId =>
    return .failed (.instanceDepthExceeded classId span #[])

/-- Try to solve a single deferred-instance constraint -/
private def trySolveDeferredInstance
    (metaId : MetaId) (domTy : Value) (span : Span) : TCM SolveResult := do
  if (← TCM.isMetaSolved metaId) then return .solved
  let forcedDom ← deepForceValue domTy
  match forcedDom with
  | .vDataType classId args =>
    trySolveResolveInstance metaId classId args.toArray span
  | _ =>
    let unsolved ← unsolvedMetasIn forcedDom
    if unsolved.isEmpty then
      return .failed (.compilerBug
        s!"deferred instance constraint on non-class type: {forcedDom}" span)
    else
      return .blocked unsolved #[]

/-- Per-constraint dispatch where instance constraints are frozen -/
private def trySolveIncrementalConstraint (c : Constraint) : TCM SolveResult := do
  match c with
  | .resolveInstance metaId _ args _ =>
    if (← TCM.isMetaSolved metaId) then return .solved
    return .blocked (← blockedMetasForInstance metaId args) #[]
  | .deferredInstance metaId domTy _ =>
    if (← TCM.isMetaSolved metaId) then return .solved
    return .blocked (← blockedMetasForInstance metaId #[domTy]) #[]
  | _ =>
    Soma.Dependent.trySolveBasicConstraint c

/-- Per-constraint dispatch with full instance resolution -/
private def trySolveDrainConstraint (c : Constraint) : TCM SolveResult := do
  match c with
  | .resolveInstance metaId classId args span =>
    TCM.withSpan span (trySolveResolveInstance metaId classId args span)
  | .deferredInstance metaId domTy span =>
    TCM.withSpan span (trySolveDeferredInstance metaId domTy span)
  | _ =>
    Soma.Dependent.trySolveBasicConstraint c

/-- Same as the drain dispatcher but blocked instances are kept -/
private def trySolveSoftConstraint (c : Constraint) : TCM SolveResult := do
  let result ← trySolveDrainConstraint c
  match c, result with
  | .resolveInstance metaId _ _ _, .failed _ => return .blocked #[metaId] #[]
  | .deferredInstance metaId _ _, .failed _ => return .blocked #[metaId] #[]
  | _, _ => return result

/-- Report constraints that survive a hard solver drain -/
private def reportStuckDrainConstraint (tc : TrackedConstraint) : TCM Unit := do
  match tc.constraint with
  | .resolveInstance _ classId args span =>
    let forcedArgs ← args.mapM deepForceValue
    let deps ← forcedArgs.foldlM (init := #[]) fun acc arg => do
      pure (acc ++ (← unsolvedMetasIn arg))
    if deps.isEmpty then
      TCM.addError (.noInstance classId forcedArgs span #[] #[])
    else
      let renderedArgs :=
        String.intercalate ", " (forcedArgs.toList.map Soma.Core.valueToString)
      TCM.addError (.cannotInfer
        s!"could not resolve instance `{classId.original} {renderedArgs}` because its type arguments remain unsolved"
        span tc.origin)
  | .deferredInstance _ domTy span =>
    let forcedDom ← deepForceValue domTy
    TCM.addError (.cannotInfer
      s!"could not resolve deferred instance `{Soma.Core.valueToString forcedDom}`"
      span tc.origin)
  | other =>
    TCM.addError (.cannotInfer
      s!"unsolved constraint after final solver drain: {other.describe}"
      other.span tc.origin)

/-- Incremental driver -/
def solveConstraints : TCM Nat := do
  let unsolved ← Unify.solveConstraintGraph trySolveIncrementalConstraint
  return unsolved.size

/-- Silent-drain driver -/
def solveConstraintsSoft : TCM SolveReport := do
  let unsolved ← Unify.solveConstraintGraph trySolveSoftConstraint
  return { mode := "soft", remaining := unsolved }

/-- Final-pass driver -/
partial def drainConstraints : TCM Unit := do
  let stateBefore ← TCM.getState
  let solvedMetasBefore ← countSolvedMetas stateBefore
  let solvedLevelsBefore := stateBefore.levelSolutions.size
  let postponedBefore := stateBefore.postponed.size
  let unsolved ← Unify.solveConstraintGraph trySolveDrainConstraint
  if unsolved.size == 0 then return
  let stateAfter ← TCM.getState
  let solvedMetasAfter ← countSolvedMetas stateAfter
  let solvedLevelsAfter := stateAfter.levelSolutions.size
  let postponedAfter := stateAfter.postponed.size
  let progress :=
    solvedMetasAfter > solvedMetasBefore ||
    solvedLevelsAfter > solvedLevelsBefore ||
    postponedAfter < postponedBefore
  if progress then drainConstraints
  else
    for tc in unsolved do
      reportStuckDrainConstraint tc
where
  countSolvedMetas (s : TCState) : TCM Nat := do
    let mut n : Nat := 0
    for (_, info) in s.metas.metas do
      if info.solution.isSome then n := n + 1
    return n

end Soma.Dependent
