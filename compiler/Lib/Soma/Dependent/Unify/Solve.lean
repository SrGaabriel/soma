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
import Soma.Dependent.Unify.Graph

open Soma.Syntax (Span)

namespace Soma.Dependent

open Soma.Core
open Soma.Dependent.Unify (SolveResult ConstraintGraph)

mutual

/-- Normalize wired primitive data type wrappers into canonical primitive types -/
private partial def normalizeWiredPrimitiveValue (v : Value) : TCM Value := do
  match v with
  | .vDataType u [] =>
    match ← TCM.lookupWiredPrimitiveOfTypeUnique u with
    | some prim => if prim.isNullary then pure (.vPrimTy prim) else pure v
    | none => pure v
  | _ => pure v

/-- Cumulative value subtyping -/
partial def subtypeUnify (v1 v2 : Value) : TCM Unit := do
  let v1f ← force v1
  let v2f ← force v2
  let v1' ← normalizeWiredPrimitiveValue v1f
  let v2' ← normalizeWiredPrimitiveValue v2f

  if valueEq v1' v2' then return

  match v1', v2' with
  | .vNeutral _ ⟨.hErrored, _⟩, _ => return
  | _, .vNeutral _ ⟨.hErrored, _⟩ => return
  | _, _ => pure ()

  match v1', v2' with
  | .vType l1, .vType l2 =>
    let ok ← subtypeLevel l1 l2
    if !ok then throwUnifyError v1' v2' "level mismatch"

  | .vPi q1 b1 n1 d1 c1, .vPi q2 b2 _ d2 c2 =>
    if q1 != q2 then throwUnifyError v1' v2' "quantity mismatch"
    if b1 != b2 then throwUnifyError v1' v2' "binder mismatch"
    subtypeUnify d2 d1
    let lvl ← TCM.currentLevel
    let x := Value.vNeutral d1 (.nVar ⟨n1, lvl⟩)
    let cod1 ← applyClosure c1 x
    let cod2 ← applyClosure c2 x
    let bindingId ← TCM.freshLocalId n1
    TCM.withBinding n1 bindingId d1 q1 b1 defaultSpan do
      subtypeUnify cod1 cod2

  | .vSigma q1 n1 f1 s1, .vSigma q2 _ f2 s2 =>
    if q1 != q2 then throwUnifyError v1' v2' "quantity mismatch"
    subtypeUnify f1 f2
    let lvl ← TCM.currentLevel
    let x := Value.vNeutral f1 (.nVar ⟨n1, lvl⟩)
    let snd1 ← applyClosure s1 x
    let snd2 ← applyClosure s2 x
    let bindingId ← TCM.freshLocalId n1
    TCM.withBinding n1 bindingId f1 q1 .explicit defaultSpan do
      subtypeUnify snd1 snd2

  | _, _ => unify v1' v2'

/-- Unify two values. May solve metavariables or postpone constraints -/
partial def unify (v1 v2 : Value) : TCM Unit := do
  -- Force both values first
  let v1f ← force v1
  let v2f ← force v2
  let v1' ← normalizeWiredPrimitiveValue v1f
  let v2' ← normalizeWiredPrimitiveValue v2f

  -- Early exit: if values are syntactically equal, no work needed
  if valueEq v1' v2' then
    return

  match v1', v2' with
  | .vNeutral _ neu1, _ =>
    if neu1.isBareHead then
      match neu1.head with
      | .hErrored => return
      | _ => pure ()
  | _, _ => pure ()
  match v2' with
  | .vNeutral _ neu2 =>
    if neu2.isBareHead then
      match neu2.head with
      | .hErrored => return
      | _ => pure ()
  | _ => pure ()

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
    let bindingId ← TCM.freshLocalId n1
    TCM.withBinding n1 bindingId d1 q1 b1 defaultSpan do
      unify cod1 cod2

  | .vLam n1 body1, .vLam _ body2 =>
    let lvl ← TCM.currentLevel
    let x := Value.vNeutral .type0 (.nVar ⟨n1, lvl⟩)
    let b1Val ← applyClosure body1 x
    let b2Val ← applyClosure body2 x
    let bindingId ← TCM.freshLocalId n1
    TCM.withBinding n1 bindingId .type0 .omega .explicit defaultSpan do
      unify b1Val b2Val

  | .vSigma q1 n1 f1 s1, .vSigma q2 _ f2 s2 =>
    if q1 != q2 then
      throwUnifyError v1' v2' "quantity mismatch"
    unify f1 f2
    let lvl ← TCM.currentLevel
    let x := Value.vNeutral f1 (.nVar ⟨n1, lvl⟩)
    let snd1 ← applyClosure s1 x
    let snd2 ← applyClosure s2 x
    let bindingId ← TCM.freshLocalId n1
    TCM.withBinding n1 bindingId f1 q1 .explicit defaultSpan do
      unify snd1 snd2

  | .vPair a1 b1, .vPair a2 b2 =>
    unify a1 a2
    unify b1 b2

  | .vPrimTy p1, .vPrimTy p2 =>
    if p1 != p2 then throwUnifyError v1' v2' "primitive type mismatch"

  | .vIntLit n1, .vIntLit n2 =>
    if n1 != n2 then throwUnifyError v1' v2' "integer mismatch"

  | .vFloatLit f1, .vFloatLit f2 =>
    if f1 != f2 then throwUnifyError v1' v2' "float mismatch"

  | .vStringLit s1, .vStringLit s2 =>
    if s1 != s2 then throwUnifyError v1' v2' "string mismatch"

  | .vLabelLit l1, .vLabelLit l2 =>
    if l1 != l2 then throwUnifyError v1' v2' "label mismatch"

  | .vRowSort, .vRowSort => pure ()
  | .vLabelSort, .vLabelSort => pure ()

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

  | .vConstructor n1 t1 as1 _, .vConstructor n2 t2 as2 _ =>
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
  | .vNeutral _ neu1, _rhs =>
    match getMetaWithSpine neu1 with
    | some (m, spine) =>
      solveMeta m spine v2
    | none =>
      match v2' with
      | .vNeutral _ neu2 => unifyNeutral neu1 neu2
      | _ => throwUnifyError v1' v2' "flex-rigid mismatch"

  -- Metavariable with spine on the right
  | _lhs, .vNeutral _ty2 neu2 =>
    match getMetaWithSpine neu2 with
    | some (m, spine) =>
      -- Pass original (pre-force) v1 so solvePattern can see abbreviation DataTypes
      solveMeta m spine v1
    | none =>
      match v1' with
      | .vNeutral _ neu1 => unifyNeutral neu1 neu2
      | _ => throwUnifyError v1' v2' "rigid-flex mismatch"

  -- Eta for functions: v1 = v2 if λx. v1 x = λx. v2 x
  | .vLam n body, other =>
    let lvl ← TCM.currentLevel
    let x := Value.vNeutral .type0 (.nVar ⟨n, lvl⟩)
    let bodyVal ← applyClosure body x
    let otherApp := Value.vNeutral .type0 (.nApp (valueToNeutral other) x)
    let bindingId ← TCM.freshLocalId n
    TCM.withBinding n bindingId .type0 .omega .explicit defaultSpan do
      unify bodyVal otherApp

  | other, .vLam n body =>
    let lvl ← TCM.currentLevel
    let x := Value.vNeutral .type0 (.nVar ⟨n, lvl⟩)
    let bodyVal ← applyClosure body x
    let otherApp := Value.vNeutral .type0 (.nApp (valueToNeutral other) x)
    let bindingId ← TCM.freshLocalId n
    TCM.withBinding n bindingId .type0 .omega .explicit defaultSpan do
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

/-- Unify two heads, throwing if the heads are incompatible -/
partial def unifyHead (h1 h2 : Head) : TCM Unit := do
  match h1, h2 with
  | .hErrored, _ => pure ()
  | _, .hErrored => pure ()
  | .hVar v1, .hVar v2 =>
    if v1.level != v2.level then
      let span ← TCM.getSpan
      TCM.throw (.unificationFailed
        (.rigidMismatch (.ofHead h1) (.ofHead h2)) .general span #[] #[])
  | .hMeta m1, .hMeta m2 =>
    if m1 != m2 then
      solveMeta m1 [] (.vNeutral .type0 (.nMeta m2))
  | .hMeta m, .hVar v =>
    solveMeta m [] (.vNeutral .type0 (.nVar v))
  | .hVar v, .hMeta m =>
    solveMeta m [] (.vNeutral .type0 (.nVar v))
  | .hConst c1 _, .hConst c2 _ =>
    if c1 != c2 then
      let span ← TCM.getSpan
      TCM.throw (.unificationFailed
        (.rigidMismatch (.ofHead h1) (.ofHead h2)) .general span #[] #[])
  | .hCase ss1 m1 as1, .hCase ss2 m2 as2 =>
    -- Two stuck cases: unify each component
    if ss1.size != ss2.size then
      let span ← TCM.getSpan
      TCM.throw (.unificationFailed
        (.rigidMismatch (.ofHead h1) (.ofHead h2)) .general span #[] #[])
    for (s1, s2) in ss1.zip ss2 do
      unify s1 s2
    unify m1 m2
    if as1.length != as2.length then
      let span ← TCM.getSpan
      TCM.throw (.unificationFailed
        (.rigidMismatch (.ofHead h1) (.ofHead h2)) .general span #[] #[])
    for (arm1, arm2) in as1.zip as2 do
      if arm1.patterns.size != arm2.patterns.size then
        let span ← TCM.getSpan
        TCM.throw (.unificationFailed
          (.rigidMismatch (.ofHead h1) (.ofHead h2)) .general span #[] #[])
      let baseLvl ← TCM.currentLevel
      let arity := arm1.patterns.foldl (fun acc p => acc + p.bindingCount) 0
      let freshArgs : Array Value := Array.ofFn (n := arity) fun i =>
        Value.vNeutral .type0 (.nVar ⟨s!"_arm_arg_{i.val}", ⟨baseLvl.lvl + i.val⟩⟩)
      let body1 ← applyArmClosureSpine arm1.closure freshArgs
      let body2 ← applyArmClosureSpine arm2.closure freshArgs
      unify body1 body2
  | _, _ =>
    let span ← TCM.getSpan
    TCM.throw (.unificationFailed
      (.rigidMismatch (.ofHead h1) (.ofHead h2)) .general span #[] #[])


/-- Unify two eliminators -/
partial def unifyElim (e1 e2 : Elim) : TCM Unit := do
  match e1, e2 with
  | .eApp a1, .eApp a2 => unify a1 a2
  | .eFst, .eFst => return
  | .eSnd, .eSnd => return
  | .eField f1, .eField f2 =>
    if f1 != f2 then
      let span ← TCM.getSpan
      TCM.throw (.unificationFailed
        (.rigidMismatch (.nFieldAccess (.ofHead (.hVar ⟨"_", ⟨0⟩⟩)) f1)
                        (.nFieldAccess (.ofHead (.hVar ⟨"_", ⟨0⟩⟩)) f2))
        .general span #[] #[])
  | _, _ =>
    let span ← TCM.getSpan
    TCM.throw (.unificationFailed
      (.rigidMismatch (.ofHead (.hVar ⟨"_", ⟨0⟩⟩))
                      (.ofHead (.hVar ⟨"_", ⟨0⟩⟩))) .general span #[] #[])

/-- Unify two neutral terms -/
partial def unifyNeutral (n1 n2 : Neutral) : TCM Unit := do
  match n1.head, n2.head with
  | .hMeta m1, _ =>
    match getMetaWithSpine n1 with
    | some (_, spineArgs) =>
      solveMeta m1 spineArgs (.vNeutral .type0 n2)
      return
    | none => pure ()
  | _, .hMeta m2 =>
    match getMetaWithSpine n2 with
    | some (_, spineArgs) =>
      solveMeta m2 spineArgs (.vNeutral .type0 n1)
      return
    | none => pure ()
  | _, _ => pure ()
  unifyHead n1.head n2.head
  if n1.spine.size != n2.spine.size then
    let span ← TCM.getSpan
    TCM.throw (.unificationFailed
      (.spineLengthMismatch n1.spine.size n2.spine.size) .general span #[] #[])
  for (e1, e2) in n1.spine.zip n2.spine do
    unifyElim e1 e2

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
      (.spineLengthMismatch vs1.length vs2.length) .general span #[] #[])
  for (v1, v2) in vs1.zip vs2 do
    unify v1 v2

/-- Cumulative level subtyping -/
partial def subtypeLevel (l1 l2 : Level) : TCM Bool := do
  let l1' := (← TCM.zonkLevel l1).simplify
  let l2' := (← TCM.zonkLevel l2).simplify
  if l1' == l2' then return true
  match l1', l2' with
  | .lit n1, .lit n2 => return n1 ≤ n2
  | .prop, _ => return true
  | _, .prop => return false
  | .lit 0, _ => return true
  | _, _ =>
    try unifyLevel l1' l2'; return true
    catch _ => return false

/-- Strict structural level unification -/
partial def unifyLevel (l1 l2 : Level) : TCM Unit := do
  let l1' ← TCM.zonkLevel l1
  let l2' ← TCM.zonkLevel l2
  let l1n := l1'.simplify
  let l2n := l2'.simplify
  if l1n == l2n then return

  match l1n, l2n with
  | .var v, rhs =>
    if rhs.freeVars.any (·.id == v.id) then
      throwUnifyError (.vType l1n) (.vType l2n) s!"occurs check: level {v} occurs in {rhs}"
    else
      TCM.solveLevelVar v rhs
  | lhs, .var v =>
    if lhs.freeVars.any (·.id == v.id) then
      throwUnifyError (.vType l1n) (.vType l2n) s!"occurs check: level {v} occurs in {lhs}"
    else
      TCM.solveLevelVar v lhs

  | .lit n1, .lit n2 =>
    throwUnifyError (.vType (.lit n1)) (.vType (.lit n2)) s!"level mismatch: {n1} ≠ {n2}"

  | .succ a, .succ b => unifyLevel a b
  | .succ a, .lit (n+1) => unifyLevel a (.lit n)
  | .lit (n+1), .succ a => unifyLevel a (.lit n)
  | .succ _, .lit 0 | .lit 0, .succ _ =>
    throwUnifyError (.vType l1n) (.vType l2n) "level mismatch: successor cannot equal 0"

  | .prop, _ | _, .prop =>
    throwUnifyError (.vType l1n) (.vType l2n) "level mismatch: Prop is distinct from Type universes (use a coercion or subtype check if cumulativity is intended)"

  | .max a b, .max c d =>
    if (a == c && b == d) || (a == d && b == c) then
      return
    else
      TCM.postpone (.levelEq l1n l2n)

  | .max a b, rhs =>
    if a == rhs then unifyLevel b rhs
    else if b == rhs then unifyLevel a rhs
    else TCM.postpone (.levelEq l1n l2n)
  | lhs, .max a b =>
    if a == lhs then unifyLevel b lhs
    else if b == lhs then unifyLevel a lhs
    else TCM.postpone (.levelEq l1n l2n)

/-- Try to solve a metavariable application: ?m spine = rhs -/
partial def solveMeta (m : MetaId) (spine : List Value) (rhs : Value) : TCM Unit := do
  -- Check if already solved
  match ← TCM.lookupMeta m with
  | some info =>
    match info.solution with
    | some sol =>
      -- Already solved: apply to spine and unify with rhs
      let applied ← applyToSpine sol spine
      -- Early exit: if applied is syntactically equal to rhs, we're done
      let rhs' ← force rhs
      if valueEq applied rhs' then
        return
      unify applied rhs'
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
    -- Force the argument too, so we work with resolved values
    let arg' ← force arg
    match v' with
    | .vLam _ body =>
      let result ← applyClosure body arg'
      applyToSpine result rest
    | .vNeutral _ty neu =>
      let resultTy ← TCM.freshMetaVal (.vType .zero)
      let applied := Value.vNeutral resultTy (.nApp neu arg')
      applyToSpine applied rest
    | .vDataType id params =>
      -- Apply type constructor to argument
      let applied := Value.vDataType id (params ++ [arg'])
      applyToSpine applied rest
    | _ =>
      let span ← TCM.getSpan
      TCM.throw (.expectedFunction v' span none)

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
    TCM.postpone (.unify (.vNeutral metaTy (buildMetaSpine m spine)) rhs span)
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

  -- Higher-kinded decomposition: ?m x₁...xₙ = T y₁...yₙ where T is a type constructor
  -- Solve ?m = T (unapplied) and unify xᵢ = yᵢ.
  -- Check the UNFORCED rhs first (preserves abbreviation DataTypes that force expands)
  let decomposeTarget? := match rhs with
    | .vDataType id params => some (Value.vDataType id [], params)
    | _ => match rhs' with
      | .vDataType id params => some (Value.vDataType id [], params)
      | _ => none
  match decomposeTarget? with
  | some (unapplied, params) =>
    if spine.length == params.length && spine.length > 0 then
      -- Check if all spine args are unsolved metas
      let allUnsolvedMetas ← spine.allM fun arg => do
        let arg' ← force arg
        match arg' with
        | .vNeutral _ (.nMeta _) => pure true
        | _ => pure false
      if allUnsolvedMetas then
        -- Decompose: solve ?m = T (unapplied) and unify spine with params
        TCM.solveMeta m unapplied (callerTag := "Solve.decompose")
        for (spineArg, param) in spine.zip params do
          unify spineArg param
        return
  | none => pure ()

  -- Check if spine is a pattern (distinct bound variables)
  match spineIsPattern ⟨spine⟩ with
  | some spineLevels =>
    let ren := PartialRenaming.fromSpine spineLevels m
    match rename ren rhs' with
    | .ok body =>
      installSolution m spineLevels body
    | .error .occursCheck =>
      let pruned ← tryOccursCheckPruning m spine rhs
      if pruned then
        let span ← TCM.getSpan
        TCM.postpone (.unify (.vNeutral metaTy (buildMetaSpine m spine)) rhs span)
      else
        let rhsForced ← force rhs
        let resolved ←
          match rhsForced with
          | .vNeutral _ neu2 =>
            match getMetaWithSpine neu2 with
            | some (m2, spine2) =>
              if m == m2 then pure false
              else tryFlexFlexIntersection m spine m2 spine2
            | none => pure false
          | _ => pure false
        if resolved then pure ()
        else
          let span ← TCM.getSpan
          TCM.throw (.unificationFailed (.occursCheck m rhs) .general span #[] #[m])
    | .error .escapeCheck =>
      let _ ← tryPrune m spine rhs
      -- If RHS is itself a pattern flex-flex, intersection may still solve it
      let rhsForced ← force rhs
      let resolved ←
        match rhsForced with
        | .vNeutral _ neu2 =>
          match getMetaWithSpine neu2 with
          | some (m2, spine2) =>
            if m == m2 then pure false
            else tryFlexFlexIntersection m spine m2 spine2
          | none => pure false
        | _ => pure false
      if !resolved then
        let span ← TCM.getSpan
        TCM.postpone (.unify (.vNeutral metaTy (buildMetaSpine m spine)) rhs span)

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
          TCM.postpone (.unify (.vNeutral metaTy (buildMetaSpine m spine)) rhs span)
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
              TCM.postpone (.unify (.vNeutral metaTy (buildMetaSpine m spine)) rhs span)
          else
            -- NEW: Different metas with spines - try spine intersection
            let intersected ← tryFlexFlexIntersection m spine m2 spine2
            if intersected then
              -- Successfully solved via intersection
              pure ()
            else
              -- Intersection failed, postpone
              let span ← TCM.getSpan
              TCM.postpone (.unify (.vNeutral metaTy (buildMetaSpine m spine)) rhs span)
        | none =>
          -- Not a meta application - postpone
          let span ← TCM.getSpan
          TCM.postpone (.unify (.vNeutral metaTy (buildMetaSpine m spine)) rhs span)
      | _ =>
        -- Not a pattern and not flex-flex - postpone
        let span ← TCM.getSpan
        TCM.postpone (.unify (.vNeutral metaTy (buildMetaSpine m spine)) rhs span)

end

/-- Try to solve a single postponed constraint, returning a detailed result -/
def trySolveConstraint (c : Constraint) : TCM SolveResult := do
  match c with
  | .unify v1 v2 span =>
    TCM.withSpan span do
      -- Force values to see if they're blocked on metas
      let v1' ← force v1
      let v2' ← force v2

      -- Check if either side is an unsolved meta - if so, we're blocked
      let blockedMetas ← collectUnsolvedMetas v1' v2'
      if !blockedMetas.isEmpty then
        -- Check if we can make progress anyway
        try
          unify v1' v2'
          return .solved
        catch e =>
          -- Check if this is a "stuck" error vs a real failure
          if blockedMetas.size > 0 then
            return .blocked blockedMetas
          else
            return .failed e
      else
        try
          unify v1' v2'
          return .solved
        catch e =>
          return .failed e

  | .subtype v1 v2 span =>
    TCM.withSpan span do
      let v1' ← force v1
      let v2' ← force v2
      let blockedMetas ← collectUnsolvedMetas v1' v2'
      try
        subtypeUnify v1' v2'
        return .solved
      catch e =>
        if !blockedMetas.isEmpty then
          return .blocked blockedMetas
        else
          return .failed e

  | .levelEq l1 l2 =>
    let l1' ← TCM.zonkLevel l1
    let l2' ← TCM.zonkLevel l2
    let l1n := l1'.simplify
    let l2n := l2'.simplify
    if l1n == l2n then return .solved
    try
      unifyLevel l1n l2n
      return .solved
    catch e =>
      return .failed e

  | .levelLe l1 l2 =>
    let l1' ← TCM.zonkLevel l1
    let l2' ← TCM.zonkLevel l2
    let l1n := l1'.simplify
    let l2n := l2'.simplify
    match l1n, l2n with
    | .lit n1, .lit n2 =>
      if n1 ≤ n2 then return .solved
      else
        let span ← TCM.getSpan
        return .failed (.internalError s!"level constraint failed: {l1n} ≤ {l2n}" span)
    | .prop, _ => return .solved -- Prop fits below every Type universe.
    | .lit 0, _ => return .solved -- 0 ≤ anything.
    | .var v, .lit n =>
      let _ := n
      TCM.solveLevelVar v (.lit 0)
      return .solved
    | .lit n, .var v =>
      TCM.solveLevelVar v (.lit n)
      return .solved
    | .var v1, .var v2 =>
      if v1.id == v2.id then return .solved
      else
        TCM.solveLevelVar v1 (.var v2)
        return .solved
    | _, _ => return .deferred

  | .resolveInstance _ _ _ _ =>
    return .deferred

  | .deferredInstance _ _ _ =>
    return .deferred
where
  /-- Collect unsolved metavariables from two values -/
  collectUnsolvedMetas (v1 v2 : Value) : TCM (Array MetaId) := do
    let mut metas : Array MetaId := #[]
    -- Check v1 for unsolved metas at the head
    match v1 with
    | .vNeutral _ (.nMeta m) =>
      let solved ← TCM.isMetaSolved m
      if !solved then metas := metas.push m
    | _ => pure ()
    -- Check v2 for unsolved metas at the head
    match v2 with
    | .vNeutral _ (.nMeta m) =>
      let solved ← TCM.isMetaSolved m
      if !solved then metas := metas.push m
    | _ => pure ()
    return metas

/-- Run the unified constraint graph solver.
    Returns the remaining unsolved constraints. -/
def solveConstraints : TCM (Array Constraint) :=
  Unify.solveConstraintGraph trySolveConstraint

end Soma.Dependent
