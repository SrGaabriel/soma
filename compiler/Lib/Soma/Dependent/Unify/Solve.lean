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

/-- Mark stuck on the union of unsolved level variables in `l1` and `l2` -/
private def markStuckOnLevels (l1 l2 : Level) : TCM Unit := do
  let lvs := (l1.freeVars ++ l2.freeVars).eraseDups.toArray
  TCM.markStuck #[] lvs

/-- Mark stuck on a meta and the unsolved metas in its spine -/
private def markStuckOnMetaSpine (m : MetaId) (spine : Array Elim) : TCM Unit := do
  let mut metas : Array MetaId := #[m]
  let mut seen : Std.HashSet Nat := { m.id }
  for e in spine do
    if let .eApp arg := e then
      for sm in Value.collectMetas arg do
        if !seen.contains sm.id then
          seen := seen.insert sm.id
          if !(← TCM.isMetaSolved sm) then metas := metas.push sm
  TCM.markStuck metas #[]

/-- Mark stuck on a meta and the unsolved metas in its spine -/
private def markStuckOnMetaWithSpineList (m : MetaId) (spine : List Value) : TCM Unit := do
  let mut metas : Array MetaId := #[m]
  let mut seen : Std.HashSet Nat := { m.id }
  for arg in spine do
    for sm in Value.collectMetas arg do
      if !seen.contains sm.id then
        seen := seen.insert sm.id
        if !(← TCM.isMetaSolved sm) then metas := metas.push sm
  TCM.markStuck metas #[]

/-- Mark stuck on a meta + Array-spine -/
private def markStuckOnMetaWithSpine (m : MetaId) (spine : Array Elim) : TCM Unit :=
  markStuckOnMetaSpine m spine

/-- Mark stuck on two metas of a flex-flex unification -/
private def markStuckOnFlexFlex (m : MetaId) (spine : List Value) (m2 : MetaId)
    : TCM Unit := do
  let mut metas : Array MetaId := #[m, m2]
  let mut seen : Std.HashSet Nat := { m.id, m2.id }
  for arg in spine do
    for sm in Value.collectMetas arg do
      if !seen.contains sm.id then
        seen := seen.insert sm.id
        if !(← TCM.isMetaSolved sm) then metas := metas.push sm
  TCM.markStuck metas #[]

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
  let lvl0 ← TCM.currentLevel
  if Soma.Core.quoteExpr lvl0 v1' == Soma.Core.quoteExpr lvl0 v2' then
    return

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

  | _, _ => unify v1 v2

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
  let lvl0 ← TCM.currentLevel
  if Soma.Core.quoteExpr lvl0 v1' == Soma.Core.quoteExpr lvl0 v2' then
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

  | .vEq _ t1 a1 b1, .vDataType id2 ps2 =>
    match ← TCM.lookupWiredIn .typeEq with
    | some info =>
      if info.name.id == id2 then
        match ps2 with
        | [t2, a2, b2] =>
          unify t1 t2
          unify a1 a2
          unify b1 b2
        | _ => throwUnifyError v1' v2' "Eq arity mismatch"
      else
        throwUnifyError v1' v2' "head mismatch"
    | none => throwUnifyError v1' v2' "head mismatch"

  | .vDataType id1 ps1, .vEq _ t2 a2 b2 =>
    match ← TCM.lookupWiredIn .typeEq with
    | some info =>
      if info.name.id == id1 then
        match ps1 with
        | [t1, a1, b1] =>
          unify t1 t2
          unify a1 a2
          unify b1 b2
        | _ => throwUnifyError v1' v2' "Eq arity mismatch"
      else
        throwUnifyError v1' v2' "head mismatch"
    | none => throwUnifyError v1' v2' "head mismatch"

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

  | .vLam n body, .vNeutral _ otherNeu =>
    let lvl ← TCM.currentLevel
    let x := Value.vNeutral .type0 (.nVar ⟨n, lvl⟩)
    let bodyVal ← applyClosure body x
    let otherApp := Value.vNeutral .type0 (.nApp otherNeu x)
    let bindingId ← TCM.freshLocalId n
    TCM.withBinding n bindingId .type0 .omega .explicit defaultSpan do
      unify bodyVal otherApp

  | .vNeutral _ otherNeu, .vLam n body =>
    let lvl ← TCM.currentLevel
    let x := Value.vNeutral .type0 (.nVar ⟨n, lvl⟩)
    let bodyVal ← applyClosure body x
    let otherApp := Value.vNeutral .type0 (.nApp otherNeu x)
    let bindingId ← TCM.freshLocalId n
    TCM.withBinding n bindingId .type0 .omega .explicit defaultSpan do
      unify otherApp bodyVal

  -- Metavariable on the left
  | .vNeutral _ (.nMeta m), rhs =>
    solveMeta m [] rhs

  -- Metavariable on the right
  | lhs, .vNeutral _ (.nMeta m) =>
    solveMeta m [] lhs

  -- Metavariable with spine on the left
  | .vNeutral neuTy1 neu1, _rhs =>
    match getMetaWithSpine neu1 with
    | some (m, spine) =>
      solveMeta m spine v2
      | none =>
        match solveMetaProjectionSpine? neu1 with
        | some (m, projSpine) =>
          solveMetaProjectionSpine m projSpine v2
        | none =>
          match v2' with
          | .vNeutral _ neu2 =>
            match getMetaWithSpine neu2 with
            | some (m, spine) =>
              solveMeta m spine v1
            | none =>
              match solveMetaProjectionSpine? neu2 with
              | some (m, projSpine) =>
                solveMetaProjectionSpine m projSpine v1
              | none =>
                unifyNeutral neu1 neu2
          | .vConstructor _ 0 ctorArgs ctorRty =>
            let ok ← recordEtaUnify ctorArgs ctorRty neuTy1 neu1 (ctorOnLeft := false)
            if !ok then throwUnifyError v1' v2' "flex-rigid mismatch"
          | _ => throwUnifyError v1' v2' "flex-rigid mismatch"

  -- Metavariable with spine on the right
  | _lhs, .vNeutral neuTy2 neu2 =>
    match getMetaWithSpine neu2 with
    | some (m, spine) =>
      -- Pass original (pre-force) v1 so solvePattern can see abbreviation DataTypes
      solveMeta m spine v1
    | none =>
      match solveMetaProjectionSpine? neu2 with
      | some (m, projSpine) =>
        solveMetaProjectionSpine m projSpine v1
      | none =>
        match v1' with
        | .vNeutral _ neu1 => unifyNeutral neu1 neu2
        | .vConstructor _ 0 ctorArgs ctorRty =>
          let ok ← recordEtaUnify ctorArgs ctorRty neuTy2 neu2 (ctorOnLeft := true)
          if !ok then throwUnifyError v1' v2' "rigid-flex mismatch"
        | _ => throwUnifyError v1' v2' "rigid-flex mismatch"

  | _, _ =>
    throwUnifyError v1' v2' "incompatible types"

/-- Unify equal-length scrutinee prefixes -/
partial def unifyScrutPrefix (ss1 ss2 : Array Value) (count : Nat) : TCM Unit := do
  if ss1.size < count || ss2.size < count then
    let span ← TCM.getSpan
    TCM.throw (.unificationFailed
      (.spineLengthMismatch ss1.size ss2.size) .general span #[] #[])
  for _h : i in [:count] do
    unify ss1[i]! ss2[i]!

/-- Stuck-case unification -/
partial def unifyHCase
    (ss1 : Array Value) (as1 : List ArmClosure)
    (ss2 : Array Value) (as2 : List ArmClosure) : TCM Bool :=
  compareHCase ss1 as1 ss2 as2 convertBodies

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
      let (younger, older) := if m1.id > m2.id then (m1, m2) else (m2, m1)
      solveMeta younger [] (.vNeutral .type0 (.nMeta older))
  | .hMeta m, .hVar v =>
    solveMeta m [] (.vNeutral .type0 (.nVar v))
  | .hVar v, .hMeta m =>
    solveMeta m [] (.vNeutral .type0 (.nVar v))
  | .hConst c1 _, .hConst c2 _ =>
    if c1 != c2 then
      let span ← TCM.getSpan
      TCM.throw (.unificationFailed
        (.rigidMismatch (.ofHead h1) (.ofHead h2)) .general span #[] #[])
  | .hCase ss1 _m1 as1, .hCase ss2 _m2 as2 =>
    let ok ← unifyHCase ss1 as1 ss2 as2
    if !ok then
      let span ← TCM.getSpan
      TCM.throw (.unificationFailed
        (.rigidMismatch (.ofHead h1) (.ofHead h2)) .general span #[] #[])
  | _, _ =>
    let span ← TCM.getSpan
    TCM.throw (.unificationFailed
      (.rigidMismatch (.ofHead h1) (.ofHead h2)) .general span #[] #[])


/-- Unify two eliminators -/
partial def unifyElim (e1 e2 : Elim) : TCM Unit := do
  match e1, e2 with
  | .eApp a1, .eApp a2 => unify a1 a2
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
      match ← splitRowAtExtending name1 (.vRowExtend l2 t2 r2) with
      | some (foundTy, restRow) =>
        unify t1 foundTy
        unify r1 restRow
      | none =>
        match ← splitRowAtExtending name2 (.vRowExtend l1 t1 r1) with
        | some (foundTy, restRow) =>
          unify t2 foundTy
          unify r2 restRow
        | none =>
          throwUnifyError (.vRowExtend l1 t1 r1) (.vRowExtend l2 t2 r2)
            s!"labels '{name1}' and '{name2}' cannot be reconciled \
               (neither row admits the other's label)"

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
      TCM.markStuck #[m1, m2] #[]

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

/-- Record-eta unification, mirrors `recordEtaConvert` for the unifier -/
partial def recordEtaUnify
    (ctorArgs : List Value) (ctorRty : Value)
    (neuTy : Value) (neu : Neutral)
    (ctorOnLeft : Bool) : TCM Bool := do
  let some ctorTypeId ← recordTypeId? ctorRty | return false
  let some neuTypeId ← recordTypeId? neuTy | return false
  if ctorTypeId != neuTypeId then return false
  let ctx ← TCM.getCtx
  let some indMeta := ctx.globals.lookupInductive ⟨ctorTypeId⟩ | return false
  if ctorArgs.length != indMeta.fieldNames.size then return false
  let projections := recordEtaProjections neu indMeta.fieldNames
  let argsArr := ctorArgs.toArray
  for _h : i in [:argsArr.size] do
    let arg := argsArr[i]!
    let proj := projections[i]!
    if ctorOnLeft then unify arg proj else unify proj arg
  return true

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
    if (a == c && b == d) || (a == d && b == c) then return
    else markStuckOnLevels l1n l2n

  | .max a b, rhs =>
    if a == rhs then unifyLevel b rhs
    else if b == rhs then unifyLevel a rhs
    else markStuckOnLevels l1n l2n
  | lhs, .max a b =>
    if a == lhs then unifyLevel b lhs
    else if b == lhs then unifyLevel a lhs
    else markStuckOnLevels l1n l2n

private partial def rowFieldsClosed (r : Value) : TCM (Option (List (String × Value))) := do
  let r ← force r
  match r with
  | .vRowEmpty => return some []
  | .vRowExtend (.vLabelLit n) ty tail =>
    match ← rowFieldsClosed tail with
    | some rest => return some ((n, ty) :: rest)
    | none => return none
  | _ => return none

partial def buildExpectedInner (innerTy : Value) (projTail : Array Elim)
    (rhs : Value) (i : Nat := 0) : TCM (Option Value) := do
  if h : i < projTail.size then
    let proj := projTail[i]'h
    let innerTy' ← force innerTy
    match proj with
    | .eField name =>
      match innerTy' with
      | .vRecord row =>
        match ← rowFieldsClosed row with
        | none => return none
        | some fields =>
          if !fields.any (·.1 == name) then return none
          let mut fieldVals : List (String × Value) := []
          let mut chosenOk := true
          for (fname, fty) in fields do
            if fname == name then
              match ← buildExpectedInner fty projTail rhs (i + 1) with
              | none => chosenOk := false
              | some chosen =>
                fieldVals := fieldVals ++ [(fname, chosen)]
            else
              let f ← TCM.freshMetaVal fty
              fieldVals := fieldVals ++ [(fname, f)]
          if chosenOk then return some (.vRecordVal fieldVals) else return none
      | _ => return none
    | .eApp _ =>
      return none
  else
    return some rhs

/-- Solve `?m spine = rhs` where `spine` may contain projection eliminators -/
partial def solveMetaProjectionSpine (m : MetaId) (spine : Array Elim) (rhs : Value)
    : TCM Unit := do
  if spine.all (fun e => match e with | .eApp _ => true | _ => false) then
    let args := spine.toList.filterMap fun e =>
      match e with | .eApp v => some v | _ => none
    solveMeta m args rhs
    return

  if h : spine.size > 0 then
    let mut leadingAppCount := 0
    let mut foundProj := false
    for h2 : i in [:spine.size] do
      if !foundProj then
        match spine[i]'h2.upper with
        | .eApp _ => leadingAppCount := leadingAppCount + 1
        | _ => foundProj := true

    if leadingAppCount == 0 then
      let firstElim := spine[0]'h
      let rest := spine.extract 1 spine.size
      match firstElim with
      | .eField fieldName => decomposeRecordMeta m fieldName rest rhs
      | .eApp _ =>
        let span ← TCM.getSpan
        TCM.throw (.internalError
          "solveMetaProjectionSpine: invariant violated (leading-app counted as projection)" span)
    else
      let leadingArgs := (spine.extract 0 leadingAppCount).toList.filterMap fun e =>
        match e with | .eApp v => some v | _ => none
      let projTail := spine.extract leadingAppCount spine.size

      match ← TCM.lookupMeta m with
      | none =>
        let span ← TCM.getSpan
        TCM.throw (.internalError s!"unknown metavariable ?{m.id}" span)
      | some info =>
        let mTy ← force info.type
        let stuck : TCM Unit := markStuckOnMetaWithSpine m spine

        let rec walkPi (ty : Value) (args : List Value) : TCM (Option Value) := do
          match args with
          | [] => return some ty
          | a :: rest =>
            let ty' ← force ty
            match ty' with
            | .vPi _ _ _ _ cod =>
              let cod' ← applyClosure cod a
              walkPi cod' rest
            | _ => return none

        match ← walkPi mTy leadingArgs with
        | none => stuck
        | some innerTy =>
          match ← buildExpectedInner innerTy projTail rhs with
          | none => stuck
          | some expectedInner => solveMeta m leadingArgs expectedInner
  else
    solveMeta m [] rhs

/-- Decompose a metavariable known to be a record -/
partial def decomposeRecordMeta (m : MetaId) (fieldName : String)
    (restSpine : Array Elim) (rhs : Value) : TCM Unit := do
  match ← TCM.lookupMeta m with
  | none =>
    let span ← TCM.getSpan
    TCM.throw (.internalError s!"unknown metavariable ?{m.id}" span)
  | some info =>
    let mTy ← force info.type
    match mTy with
    | .vRecord row =>
      let rec rowFields (r : Value) : Option (List (String × Value)) :=
        match r with
        | .vRowEmpty => some []
        | .vRowExtend (.vLabelLit name) ty tail => do
          let rest ← rowFields tail
          some ((name, ty) :: rest)
        | _ => none
      match rowFields row with
      | none =>
        markStuckOnMetaSpine m restSpine
      | some fields =>
        if !fields.any (·.1 == fieldName) then
          let span ← TCM.getSpan
          TCM.throw (.fieldNotFound fieldName mTy span #[] none)
        else
          let mut fieldMetas : List (String × Value) := []
          let mut chosenId? : Option MetaId := none
          for (name, ty) in fields do
            let mFieldVal ← TCM.freshMetaVal ty
            fieldMetas := fieldMetas ++ [(name, mFieldVal)]
            if name == fieldName then
              match mFieldVal with
              | .vNeutral _ ⟨.hMeta id, _⟩ => chosenId? := some id
              | _ => pure ()
          solveMeta m [] (.vRecordVal fieldMetas)
          match chosenId? with
          | some chosenId => solveMetaProjectionSpine chosenId restSpine rhs
          | none =>
            let span ← TCM.getSpan
            TCM.throw (.internalError "freshMetaVal returned non-meta value" span)
    | _ =>
      markStuckOnMetaSpine m restSpine

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
    markStuckOnMetaWithSpineList m spine
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

  let decomposeTarget? := match rhs with
    | .vDataType id params => some (Value.vDataType id [], params)
    | _ => match rhs' with
      | .vDataType id params => some (Value.vDataType id [], params)
      | _ => none
  match decomposeTarget? with
  | some (unapplied, params) =>
    if spine.length == params.length && spine.length > 0 then
      let attempt : TCM Unit := do
        TCM.solveMeta m unapplied (callerTag := "Solve.decompose")
        for (spineArg, param) in spine.zip params do
          unify spineArg param
      match ← TCM.tryWithRollback attempt with
      | some _ => return
      | none   => pure ()
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
        markStuckOnMetaWithSpineList m spine
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
        markStuckOnMetaWithSpineList m spine

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
        if m == m2 then
          pure ()
        else
          -- Different metas: try pruning both or postpone
          let _ ← tryPrune m spine rhs
          markStuckOnFlexFlex m spine m2
      | .vNeutral _ neu2 =>
        match getMetaWithSpine neu2 with
        | some (m2, spine2) =>
          -- Flex-flex with spines: ?m spine1 = ?m2 spine2
          if m == m2 then
            if spine.length == spine2.length then
              -- Try to unify the spines
              for (v1, v2) in spine.zip spine2 do
                unify v1 v2
            else
              markStuckOnMetaWithSpineList m spine
          else
            let intersected ← tryFlexFlexIntersection m spine m2 spine2
            if !intersected then
              markStuckOnFlexFlex m spine m2
        | none =>
          markStuckOnMetaWithSpineList m spine
      | _ =>
        markStuckOnMetaWithSpineList m spine

end

/-- Run a unification action under the constraint-graph dispatch envelope -/
private def runUnifyAction (action : TCM Unit) : TCM SolveResult := do
  TCM.clearStuckSignal
  try
    action
    match ← TCM.getStuckSignal with
    | some (m, lv) =>
      TCM.clearStuckSignal
      return .blocked m lv
    | none => return .solved
  catch e => return .failed e

/-- Try to solve a single non-instance constraint -/
def trySolveBasicConstraint (c : Constraint) : TCM SolveResult := do
  match c with
  | .unify v1 v2 span =>
    TCM.withSpan span do
      -- Force values to see if they're blocked on metas
      let v1' ← force v1
      let v2' ← force v2
      runUnifyAction (unify v1' v2')

  | .subtype v1 v2 span =>
    TCM.withSpan span do
      let v1' ← force v1
      let v2' ← force v2
      runUnifyAction (subtypeUnify v1' v2')

  | .levelEq l1 l2 =>
    let l1n := (← TCM.zonkLevel l1).simplify
    let l2n := (← TCM.zonkLevel l2).simplify
    if l1n == l2n then return .solved
    runUnifyAction (unifyLevel l1n l2n)

  | .levelLe l1 l2 =>
    let l1n := (← TCM.zonkLevel l1).simplify
    let l2n := (← TCM.zonkLevel l2).simplify
    match l1n, l2n with
    | .lit n1, .lit n2 =>
      if n1 ≤ n2 then return .solved
      else
        let span ← TCM.getSpan
        return .failed (.internalError s!"level constraint failed: {l1n} ≤ {l2n}" span)
    | .prop, _ => return .solved   -- Prop fits below every Type universe.
    | .lit 0, _ => return .solved  -- 0 ≤ anything.
    | .var v, .lit _ => TCM.solveLevelVar v (.lit 0); return .solved
    | .lit n, .var v => TCM.solveLevelVar v (.lit n); return .solved
    | .var v1, .var v2 =>
      if v1.id == v2.id then return .solved
      else TCM.solveLevelVar v1 (.var v2); return .solved
    | _, _ =>
      let lvs := (l1n.freeVars ++ l2n.freeVars).eraseDups.toArray
      if lvs.isEmpty then return .deferred
      else return .blocked #[] lvs

  | .resolveInstance metaId _ _ _ =>
    return .blocked #[metaId] #[]
  | .deferredInstance metaId _ _ =>
    return .blocked #[metaId] #[]

end Soma.Dependent
