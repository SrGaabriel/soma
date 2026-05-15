import Soma.Core.Value
import Soma.Core.Eval
import Soma.Dependent.Prelude
import Soma.Dependent.Monad
import Soma.Dependent.Unify.Core

namespace Soma.Dependent

open Soma.Core

/-- Enumerate a list with indices starting from 0 (for pruning) -/
def enumListForPrune {α : Type} (xs : List α) : List (Nat × α) :=
  let rec go (i : Nat) : List α → List (Nat × α)
    | [] => []
    | x :: rest => (i, x) :: go (i + 1) rest
  go 0 xs

/-- Extract parameter types from a Pi type -/
partial def extractMetaParamTypes (ty : Value) : TCM (List Value) := do
  go ty []
where
  go (ty : Value) (acc : List Value) : TCM (List Value) := do
    let ty' ← force ty
    match ty' with
    | .vPi _ _ name dom cod =>
      -- Apply closure to a dummy value to get the codomain
      let lvl ← TCM.currentLevel
      let dummyArg := Value.vNeutral dom (.nVar ⟨name, lvl⟩)
      let codTy ← applyClosure cod dummyArg
      go codTy (dom :: acc)
    | _ => return acc.reverse

/-- Get the result type of a Pi type (after all parameters) -/
partial def getMetaResultType (ty : Value) : TCM Value := do
  let ty' ← force ty
  match ty' with
  | .vPi _ _ name dom cod =>
    let lvl ← TCM.currentLevel
    let dummyArg := Value.vNeutral dom (.nVar ⟨name, lvl⟩)
    let codTy ← applyClosure cod dummyArg
    getMetaResultType codTy
  | _ => return ty'

/-- Evaluate a pruning solution Expr to a Value -/
def evalPruneSolution (e : Soma.Core.Expr) : TCM Value := TCM.evalExpr e

/-- Build a Pi type from a list of domain types, with a given codomain.
    buildPiType [A, B, C] D = A -> B -> C -> D -/
def buildPiType (doms : List Value) (cod : Value) : TCM Value := do
  match doms with
  | [] => return cod
  | dom :: rest =>
    let restTy ← buildPiType rest cod
    let codClos := Closure.const "_" restTy
    return Value.vPi .omega .explicit "_" dom codClos

/-- Build nested lambdas from parameter names and a body expression.
    buildLambdas ["x", "y"] body = λx. λy. body -/
def buildLambdasFromNames (names : List String) (body : Soma.Core.Expr) : Soma.Core.Expr :=
  names.foldr (fun name acc => .lam .explicit name (.sort Level.zero) acc) body

/-- Build an Expr that applies a meta to selected arguments.
    Given neededIndices = [0, 2] and paramCount = 3, builds:
    ?m' (bvar 2) (bvar 0)  -- using de Bruijn indices -/
def buildFilteredApplication (newMetaId : MetaId) (neededIndices : List Nat) (paramCount : Nat) : Soma.Core.Expr :=
  let args := neededIndices.map fun idx =>
    -- Convert spine position to de Bruijn index
    -- If we have params x0, x1, x2 (bound left to right), then:
    -- x0 has index paramCount-1, x1 has index paramCount-2, etc.
    Soma.Core.Expr.bvar (paramCount - idx - 1)
  args.foldl (fun acc arg => .app acc arg) (.mvar ⟨newMetaId.id⟩)

/-- Try to prune a metavariable: restrict its domain by eliminating
    variables that cannot appear in its solution.

    When solving `?m spine = rhs` where some spine variables don't appear in rhs,
    we can sometimes create a more restricted meta.

    For example, if we have `?m x y z = e` where `e` only mentions `x` and `z`:
    1. Create a new meta `?m' : A -> C -> R` (skipping B, the type of y)
    2. Solve `?m := λx y z. ?m' x z`
    3. Return `?m'` so unification can continue with the simpler problem

    Returns Some newMeta if pruning was successful, None if not applicable. -/
def tryPrune (m : MetaId) (spine : List Value) (rhs : Value) : TCM (Option MetaId) := do
  -- Get the meta's type
  let info? ← TCM.lookupMeta m
  match info? with
  | none => return none
  | some info =>
    -- Only prune if meta is unsolved
    if info.solution.isSome then return none

    -- Collect levels that appear in the RHS
    let rhsVars := collectFreeVars rhs |>.toList.eraseDups

    -- Collect levels from the spine (with their positions)
    let spineLevelsWithIdx : List (Nat × DeBruijnLvl) :=
      (enumListForPrune spine).filterMap fun (idx, arg) =>
        match asBoundVar arg with
        | some lvl => some (idx, lvl)
        | none => none

    -- Find which spine positions have variables that appear in RHS (needed)
    -- and which don't (prunable)
    let neededPositions : List (Nat × DeBruijnLvl) :=
      spineLevelsWithIdx.filter fun (_, lvl) => rhsVars.contains lvl
    let prunablePositions : List (Nat × DeBruijnLvl) :=
      spineLevelsWithIdx.filter fun (_, lvl) => !rhsVars.contains lvl

    if prunablePositions.isEmpty then
      -- Nothing to prune
      return none
    else if neededPositions.length == spineLevelsWithIdx.length then
      -- All positions are needed, no pruning possible
      return none
    else
      -- Extract the types of needed parameters from the meta's type
      -- The meta's type should be a nested Pi: A₀ -> A₁ -> ... -> Aₙ -> R
      let neededIndices : List Nat := neededPositions.map (fun p => p.1)

      -- Walk the meta's type to extract parameter types
      let allParamTypes ← extractMetaParamTypes info.type

      -- If meta's type doesn't have enough Pi layers to match the spine, can't prune
      if allParamTypes.length < spine.length then
        return none

      let resultTy ← getMetaResultType info.type

      -- Filter to only the needed parameter types
      let indexedParamTypes : List (Nat × Value) := enumListForPrune allParamTypes
      let neededParamTypes : List (Nat × Value) := indexedParamTypes.filter fun (idx, _) =>
        neededIndices.contains idx
      let neededDoms : List Value := neededParamTypes.map (fun p => p.2)

      -- Build the new restricted Pi type: neededDom₀ -> neededDom₁ -> ... -> R
      let newMetaType ← buildPiType neededDoms resultTy

      -- Create the new meta with the restricted type
      let newMetaId ← TCM.freshMeta newMetaType

      -- Build the solution for the old meta:
      -- ?m := λx₀ x₁ ... xₙ. ?m' (filter needed xᵢ)
      let paramCount := allParamTypes.length
      let paramNames := (List.range paramCount).map fun i => s!"x{i}"

      -- Build application of new meta to only the needed arguments
      let appTerm := buildFilteredApplication newMetaId neededIndices paramCount

      -- Wrap in lambdas for all original parameters
      let solutionTerm := buildLambdasFromNames paramNames appTerm

      -- Evaluate the solution term to a Value
      let solutionVal ← evalPruneSolution solutionTerm

      -- Solve the old meta with this solution
      TCM.solveMeta m solutionVal (callerTag := "Pruning.pruneMeta")

      return some newMetaId

/-- Compute the intersection of two spines as (level, position in spine1, position in spine2).
    Only includes levels that appear as distinct bound variables in both spines. -/
def computeSpineIntersection (spine1 spine2 : List Value)
    : List (DeBruijnLvl × Nat × Nat) :=
  let withIdx1 := enumListForPrune spine1
  let withIdx2 := enumListForPrune spine2
  -- Get (position, level) pairs for each spine
  let levels1 := withIdx1.filterMap fun (idx, v) =>
    match asBoundVar v with
    | some lvl => some (idx, lvl)
    | none => none
  let levels2 := withIdx2.filterMap fun (idx, v) =>
    match asBoundVar v with
    | some lvl => some (idx, lvl)
    | none => none
  -- Find common levels
  levels1.filterMap fun (idx1, lvl) =>
    match levels2.find? fun (_, lvl2) => lvl == lvl2 with
    | some (idx2, _) => some (lvl, idx1, idx2)
    | none => none

/-- Try flex-flex unification via spine intersection.
    When `?m1 spine1 = ?m2 spine2`, we:
    1. Compute the intersection of variables in both spines
    2. Create a new meta `?W` that takes only the intersection
    3. Solve `?m1 := λspine1. ?W intersection1` and `?m2 := λspine2. ?W intersection2`
    Returns true if intersection-based solving was possible. -/
def tryFlexFlexIntersection (m1 : MetaId) (spine1 : List Value)
    (m2 : MetaId) (spine2 : List Value) : TCM Bool := do
  -- Get meta info for both
  let info1? ← TCM.lookupMeta m1
  let info2? ← TCM.lookupMeta m2
  match info1?, info2? with
  | some info1, some info2 =>
    -- Both must be unsolved
    if info1.solution.isSome || info2.solution.isSome then return false

    -- Compute intersection
    let intersection := computeSpineIntersection spine1 spine2
    if intersection.isEmpty then
      -- No common variables - can only solve if both return the same constant
      return false

    -- Extract the types of intersection parameters from m1's type
    let allParamTypes1 ← extractMetaParamTypes info1.type
    let resultTy1 ← getMetaResultType info1.type

    -- Get intersection indices for spine1
    let intersectionIndices1 : List Nat := intersection.map (·.2.1)

    -- Filter to only intersection parameter types
    let indexedParams1 := enumListForPrune allParamTypes1
    let intersectionParams := indexedParams1.filter fun (idx, _) =>
      intersectionIndices1.contains idx
    let intersectionDoms := intersectionParams.map (·.2)

    -- Create the intersection meta ?W with type built from intersection params
    let newMetaType ← buildPiType intersectionDoms resultTy1
    let newMetaId ← TCM.freshMeta newMetaType

    -- Build solution for m1: λspine1. ?W (intersection args from spine1)
    let paramCount1 := allParamTypes1.length
    let paramNames1 := (List.range paramCount1).map fun i => s!"x{i}"
    let appTerm1 := buildFilteredApplication newMetaId intersectionIndices1 paramCount1
    let solution1 := buildLambdasFromNames paramNames1 appTerm1
    let solution1Val ← evalPruneSolution solution1
    TCM.solveMeta m1 solution1Val (callerTag := "Pruning.m1")

    -- Build solution for m2: λspine2. ?W (intersection args from spine2)
    let allParamTypes2 ← extractMetaParamTypes info2.type
    let intersectionIndices2 : List Nat := intersection.map (·.2.2)
    let paramCount2 := allParamTypes2.length
    let paramNames2 := (List.range paramCount2).map fun i => s!"y{i}"
    let appTerm2 := buildFilteredApplication newMetaId intersectionIndices2 paramCount2
    let solution2 := buildLambdasFromNames paramNames2 appTerm2
    let solution2Val ← evalPruneSolution solution2
    TCM.solveMeta m2 solution2Val (callerTag := "Pruning.m2")

    return true
  | _, _ => return false

/-- Information about a twin variable pair -/
structure TwinVar where
  /-- The original level -/
  originalLevel : DeBruijnLvl
  /-- The name from the first occurrence -/
  name1 : String
  /-- The name from the second occurrence (may differ) -/
  name2 : String
  deriving Inhabited

/-- Collect the "depth" at which a meta occurs in a value.
    Depth 0 means top-level, depth 1 means under one constructor, etc.
    Also collects which spine arguments are "in scope" at each occurrence. -/
structure MetaOccurrence where
  /-- Nesting depth of this occurrence -/
  depth : Nat
  /-- Variables that are in scope at this occurrence -/
  scopeVars : Array DeBruijnLvl
  deriving Inhabited

mutual

/-- Collect all occurrences of a meta in a value, with scope info -/
partial def collectMetaOccurrences (m : MetaId) (v : Value) (depth : Nat)
    (scope : Array DeBruijnLvl) : Array MetaOccurrence :=
  match v with
  | .vType _ => #[]
  | .vPi _ _ _ dom cod =>
    collectMetaOccurrences m dom depth scope ++
    collectMetaOccurrencesClosure m cod (depth + 1) scope
  | .vLam _ body =>
    collectMetaOccurrencesClosure m body (depth + 1) scope
  | .vNeutral _ neu => collectMetaOccurrencesNeutral m neu depth scope
  | .vRowExtend label ty tail =>
    collectMetaOccurrences m label depth scope ++
    collectMetaOccurrences m ty (depth + 1) scope ++
    collectMetaOccurrences m tail depth scope
  | .vRecord row => collectMetaOccurrences m row depth scope
  | .vVariant row => collectMetaOccurrences m row depth scope
  | .vRecordVal fields =>
    fields.foldl (fun acc (_, v) =>
      acc ++ collectMetaOccurrences m v (depth + 1) scope) #[]
  | .vDataType _ params =>
    params.foldl (fun acc p =>
      acc ++ collectMetaOccurrences m p (depth + 1) scope) #[]
  | .vConstructor _ _ args _ =>
    args.foldl (fun acc a =>
      acc ++ collectMetaOccurrences m a (depth + 1) scope) #[]
  | _ => #[]

partial def collectMetaOccurrencesNeutral (m : MetaId) (n : Neutral) (depth : Nat)
    (scope : Array DeBruijnLvl) : Array MetaOccurrence :=
  collectMetaOccurrencesHead m n.head depth scope ++
    n.spine.foldl (fun acc e =>
      acc ++ collectMetaOccurrencesElim m e (depth + 1) scope) #[]

partial def collectMetaOccurrencesHead (m : MetaId) (h : Head) (depth : Nat)
    (scope : Array DeBruijnLvl) : Array MetaOccurrence :=
  match h with
  | .hVar _ => #[]
  | .hConst _ _ => #[]
  | .hErrored => #[]
  | .hMeta id =>
    if id == m then #[{ depth := depth, scopeVars := scope }]
    else #[]
  | .hCase scrutinees motive arms =>
    scrutinees.foldl (fun acc s =>
      acc ++ collectMetaOccurrences m s depth scope) #[] ++
    collectMetaOccurrences m motive depth scope ++
    arms.foldl (fun acc arm =>
      acc ++ collectMetaOccurrencesClosure m arm.closure (depth + 1) scope) #[]

partial def collectMetaOccurrencesElim (m : MetaId) (e : Elim) (depth : Nat)
    (scope : Array DeBruijnLvl) : Array MetaOccurrence :=
  match e with
  | .eApp arg => collectMetaOccurrences m arg depth scope
  | .eField _ => #[]

partial def collectMetaOccurrencesClosure (m : MetaId) (clos : Closure) (depth : Nat)
    (scope : Array DeBruijnLvl) : Array MetaOccurrence :=
  match clos with
  | .const _ value => collectMetaOccurrences m value depth scope
  | .term _ env _ =>
    -- The closure introduces a new variable, extend scope
    let extendedScope := scope.push ⟨env.size⟩
    env.values.foldl (fun acc (_, v) =>
      acc ++ collectMetaOccurrences m v depth extendedScope) #[]

end

/-- Recovery hook for occurs check failures -/
def tryOccursCheckPruning (_m : MetaId) (_spine : List Value) (_rhs : Value)
    : TCM Bool := do
  return false

/-- Record that meta1 depends on meta2 (meta2's solution is needed to solve meta1) -/
def recordMetaDependency (meta1 meta2 : MetaId) : TCM Unit := do
  TCM.modifyState fun s => { s with metas := s.metas.addDependency meta1 meta2 }

/-- Check if solving this meta should be deferred because its type is unsolved -/
def shouldDeferMeta (m : MetaId) : TCM Bool := do
  match ← TCM.lookupMeta m with
  | none => return false
  | some info =>
    -- Check if the type contains unsolved metas
    let typeMetas := Value.collectMetas info.type
    for mid in typeMetas do
      let solved ← TCM.isMetaSolved mid
      if !solved then
        -- Record the dependency
        recordMetaDependency m mid
        return true
    return false

/-- Check if a spine can be made into a pattern by η-expanding the meta.
    Returns the extended spine and corresponding RHS if successful. -/
def tryMakePatternViaEta (m : MetaId) (spine : List Value) (rhs : Value)
    : TCM (Option (List Value × Value)) := do
  -- First check: is the RHS a lambda?
  match rhs with
  | .vLam name body =>
    -- Create a fresh variable to extend the spine
    let lvl ← TCM.currentLevel
    let x := Value.vNeutral .type0 (.nVar ⟨name, lvl⟩)
    -- Apply the closure to get the body
    let bodyVal ← applyClosure body x
    -- Check if adding x to spine makes it a pattern
    let extendedSpine := spine ++ [x]
    match spineIsPattern ⟨extendedSpine⟩ with
    | some _ =>
      -- Success! The extended spine is a pattern
      -- But we need to check occurs check
      if occursIn m bodyVal then
        return none  -- Would cause infinite type
      else
        return some (extendedSpine, bodyVal)
    | none =>
      -- Still not a pattern - try recursively
      return none
  | _ => return none

end Soma.Dependent
