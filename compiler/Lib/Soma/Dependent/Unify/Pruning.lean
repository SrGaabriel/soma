import Soma.Core.Value
import Soma.Core.Eval
import Soma.Dependent.Prelude
import Soma.Dependent.Monad
import Soma.Dependent.Unify.Core

namespace Soma.Dependent

open Soma.Core

/-- Determine which variables from the spine can potentially appear in the RHS.
    Returns the "safe" levels that can be part of the solution. -/
def computeSafeScope (spine : List Value) (rhs : Value) : List DeBruijnLvl :=
  let rhsFreeVars := collectFreeVars rhs
  -- A level is safe if it either:
  -- 1. Appears in the spine (can be referenced through the lambda binding), OR
  -- 2. Does not appear free in the RHS at all
  let spineLevels := spine.filterMap asBoundVar
  spineLevels.filter fun lvl =>
    rhsFreeVars.contains lvl || !rhsFreeVars.any (· == lvl)

/-- Enumerate a list with indices starting from 0 (for pruning) -/
def enumListForPrune {α : Type} (xs : List α) : List (Nat × α) :=
  let rec go (i : Nat) : List α → List (Nat × α)
    | [] => []
    | x :: rest => (i, x) :: go (i + 1) rest
  go 0 xs

/-- Extract parameter types from a Pi type (non-recursive, uses fuel) -/
partial def extractMetaParamTypes (ty : Value) : TCM (List Value) := do
  let rec go (fuel : Nat) (ty : Value) (acc : List Value) : TCM (List Value) := do
    if fuel == 0 then return acc.reverse
    let ty' ← force ty
    match ty' with
    | .vPi _ _ name dom cod =>
      -- Apply closure to a dummy value to get the codomain
      let lvl ← TCM.currentLevel
      let dummyArg := Value.vNeutral dom (.nVar ⟨name, lvl⟩)
      let codTy ← applyClosure cod dummyArg
      go (fuel - 1) codTy (dom :: acc)
    | _ => return acc.reverse
  go maxPiParams ty []

/-- Get the result type of a Pi type (after all parameters) -/
partial def getMetaResultType (ty : Value) : TCM Value := do
  let rec go (fuel : Nat) (ty : Value) : TCM Value := do
    if fuel == 0 then return ty
    let ty' ← force ty
    match ty' with
    | .vPi _ _ name dom cod =>
      let lvl ← TCM.currentLevel
      let dummyArg := Value.vNeutral dom (.nVar ⟨name, lvl⟩)
      let codTy ← applyClosure cod dummyArg
      go (fuel - 1) codTy
    | _ => return ty'
  go maxPiParams ty

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
      TCM.solveMeta m solutionVal

      return some newMetaId

/-! ## Spine Intersection for Flex-Flex Unification

When unifying `?X spine1 = ?Y spine2` where both are metas with different spines,
we compute the intersection of variables that appear in both spines. This allows
us to prune both metas to only depend on the common variables.

For example:
  ?X x y = ?Y x z
  Intersection: {x}
  Result: Create ?W : A -> R, then ?X := λx y. ?W x, ?Y := λx z. ?W x
-/

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
    TCM.solveMeta m1 solution1Val

    -- Build solution for m2: λspine2. ?W (intersection args from spine2)
    let allParamTypes2 ← extractMetaParamTypes info2.type
    let intersectionIndices2 : List Nat := intersection.map (·.2.2)
    let paramCount2 := allParamTypes2.length
    let paramNames2 := (List.range paramCount2).map fun i => s!"y{i}"
    let appTerm2 := buildFilteredApplication newMetaId intersectionIndices2 paramCount2
    let solution2 := buildLambdasFromNames paramNames2 appTerm2
    let solution2Val ← evalPruneSolution solution2
    TCM.solveMeta m2 solution2Val

    return true
  | _, _ => return false

/-! ## Twin Variables for Dependent Pattern Matching

When pattern matching introduces variables with dependent types, we may have
situations like:
  match xs with
  | Cons (x : a) (xs' : Vec n a) => ...

Here `a` and `n` are pattern variables, and `xs' : Vec n a` depends on both.
When type-checking, we might generate constraints like:
  ?X n a = Vec n a

The key insight is that if `?X`'s solution would need to mention `n` and `a`,
and those are exactly the spine variables, then we can solve directly.

Twin variables are pairs of variables that must be unified together because
they represent the same pattern variable appearing in different contexts. -/

/-- Information about a twin variable pair -/
structure TwinVar where
  /-- The original level -/
  originalLevel : DeBruijnLvl
  /-- The name from the first occurrence -/
  name1 : String
  /-- The name from the second occurrence (may differ) -/
  name2 : String
  deriving Inhabited

/-- Detect if a constraint involves twin variables.
    Returns the pairs of variables that are twins. -/
def detectTwinVars (spine : List Value) (rhs : Value) : List TwinVar :=
  let spineLevels := spine.filterMap asBoundVar
  let rhsFreeVars := collectFreeVars rhs
  -- Variables are twins if they appear in both spine and rhs with the same level
  spineLevels.filterMap fun lvl =>
    if rhsFreeVars.contains lvl then
      -- Find the name from the spine
      let name := match spine.find? (fun v => asBoundVar v == some lvl) with
        | some (.vNeutral _ (.nVar v)) => v.name
        | _ => s!"twin{lvl.lvl}"
      some { originalLevel := lvl, name1 := name, name2 := name }
    else
      none

/-- Check if all free variables in the RHS are covered by twin variables.
    If so, the pattern is solvable via identity substitution. -/
def allVarsCoveredByTwins (twins : List TwinVar) (rhs : Value) : Bool :=
  let twinLevels := twins.map (·.originalLevel)
  let rhsFreeVars := collectFreeVars rhs
  rhsFreeVars.all fun lvl => twinLevels.contains lvl

/-! ## Occurs Check with Pruning

When the occurs check fails (e.g., ?X = List ?X), we can sometimes recover
by pruning the problematic argument. This is useful when the occurrence is
under a lambda that doesn't use all spine variables.

For example:
  ?X x = Pair x (?X x)  -- fails occurs check
But:
  ?X x = Pair x ?Y      -- ?Y doesn't depend on x
If we can show ?X x only appears where x is not used, we can prune. -/

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
  | .vSigma _ _ fst snd =>
    collectMetaOccurrences m fst depth scope ++
    collectMetaOccurrencesClosure m snd (depth + 1) scope
  | .vPair a b =>
    collectMetaOccurrences m a (depth + 1) scope ++
    collectMetaOccurrences m b (depth + 1) scope
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
  | .vConstructor _ _ args =>
    args.foldl (fun acc a =>
      acc ++ collectMetaOccurrences m a (depth + 1) scope) #[]
  | .vEq _ ty lhs rhs =>
    collectMetaOccurrences m ty depth scope ++
    collectMetaOccurrences m lhs (depth + 1) scope ++
    collectMetaOccurrences m rhs (depth + 1) scope
  | .vRefl ty x =>
    collectMetaOccurrences m ty depth scope ++
    collectMetaOccurrences m x (depth + 1) scope
  | .vTransport _ ty motive lhs rhs eq body =>
    collectMetaOccurrences m ty depth scope ++
    collectMetaOccurrences m motive (depth + 1) scope ++
    collectMetaOccurrences m lhs (depth + 1) scope ++
    collectMetaOccurrences m rhs (depth + 1) scope ++
    collectMetaOccurrences m eq (depth + 1) scope ++
    collectMetaOccurrences m body (depth + 1) scope
  | _ => #[]

partial def collectMetaOccurrencesNeutral (m : MetaId) (n : Neutral) (depth : Nat)
    (scope : Array DeBruijnLvl) : Array MetaOccurrence :=
  match n with
  | .nVar _ => #[]
  | .nMeta id =>
    if id == m then #[{ depth := depth, scopeVars := scope }]
    else #[]
  | .nApp fn arg =>
    collectMetaOccurrencesNeutral m fn depth scope ++
    collectMetaOccurrences m arg (depth + 1) scope
  | .nFst pair => collectMetaOccurrencesNeutral m pair depth scope
  | .nSnd pair => collectMetaOccurrencesNeutral m pair depth scope
  | .nFieldAccess rec _ => collectMetaOccurrencesNeutral m rec depth scope
  | .nCase scrut arms =>
    collectMetaOccurrencesNeutral m scrut depth scope ++
    arms.foldl (fun acc arm =>
      acc ++ collectMetaOccurrencesClosure m arm.closure (depth + 1) scope) #[]

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

/-- Try to recover from occurs check failure by pruning.
    If the meta occurs but only at positions where some spine variables aren't used,
    we might be able to prune those variables from the meta's domain.
    Returns true if pruning was attempted (caller should retry unification). -/
def tryOccursCheckPruning (m : MetaId) (spine : List Value) (rhs : Value) : TCM Bool := do
  -- Collect all occurrences of the meta
  let occurrences := collectMetaOccurrences m rhs 0 #[]
  if occurrences.isEmpty then
    return false  -- No occurrences (shouldn't happen if occurs check triggered)

  -- Get spine levels
  let spineLevels : Array DeBruijnLvl := spine.filterMap asBoundVar |>.toArray

  -- Check if there are any spine variables that are NOT in scope at any occurrence
  -- These could potentially be pruned
  let prunableLevels := spineLevels.filter fun lvl =>
    occurrences.all fun occ => !occ.scopeVars.contains lvl

  if prunableLevels.isEmpty then
    return false  -- All spine vars are needed at some occurrence

  -- Try pruning these variables
  let rhsWithoutMeta := rhs  -- We'd need to substitute the meta occurrences
  let _ ← tryPrune m spine.toArray.toList rhsWithoutMeta

  return true

/-! ## Heterogeneous Constraint Handling

When we have constraints involving metas whose types are also metas, we need
to be careful about solving order. We track these dependencies and solve
the type metas first. -/

/-- Check if a value's type involves unsolved metavariables -/
def hasMetaType (v : Value) : TCM Bool := do
  match v with
  | .vNeutral ty _ =>
    let metas := collectMetas ty
    metas.anyM fun mid => do
      let solved ← TCM.isMetaSolved mid
      return !solved
  | _ => return false

/-- Record that meta1 depends on meta2 (meta2's solution is needed to solve meta1) -/
def recordMetaDependency (meta1 meta2 : MetaId) : TCM Unit := do
  TCM.modifyState fun s => { s with metas := s.metas.addDependency meta1 meta2 }

/-- Check if solving this meta should be deferred because its type is unsolved -/
def shouldDeferMeta (m : MetaId) : TCM Bool := do
  match ← TCM.lookupMeta m with
  | none => return false
  | some info =>
    -- Check if the type contains unsolved metas
    let typeMetas := collectMetas info.type
    for mid in typeMetas do
      let solved ← TCM.isMetaSolved mid
      if !solved then
        -- Record the dependency
        recordMetaDependency m mid
        return true
    return false

/-! ## Eta Expansion Helpers -/

/-- Try η-expansion on a lambda to potentially create a pattern.
    If `rhs = λx. body` and we have `?m spine = rhs`, we can try to solve
    `?m spine x = body` instead, which might be a pattern. -/
def tryEtaExpandLambda (rhs : Value) : Option (String × Value × Value) :=
  match rhs with
  | .vLam name _body =>
    -- We can η-expand: instead of ?m = λx. body, solve ?m x = body
    -- where body is the closure applied to a fresh variable
    some (name, .type0, .vNeutral .type0 (.nVar ⟨name, ⟨0⟩⟩))  -- Placeholder, actual application done in caller
  | _ => none

/-- Try η-expansion on a pair -/
def tryEtaExpandPair (rhs : Value) : Option (Value × Value) :=
  match rhs with
  | .vPair a b => some (a, b)
  | .vNeutral ty neu =>
    -- η-expand: x = (fst x, snd x)
    some (.vNeutral ty (.nFst neu), .vNeutral ty (.nSnd neu))
  | _ => none

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
