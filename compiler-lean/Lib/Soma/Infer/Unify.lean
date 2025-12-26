import Soma.Infer.Error
import Soma.Infer.Substitution

namespace Soma.Infer

open Soma.Typing
open Soma.Syntax

/-- Result of unification -/
abbrev UnifyResult := Except InferError Subst

/-- Context for unification operations -/
structure UnifyContext where
  /-- The purpose of this unification (for error messages) -/
  purpose : UnifyPurpose
  /-- Span of the "expected" type -/
  expectedSpan : Span
  /-- Span of the "actual" type -/
  actualSpan : Span

namespace Unify

mutual
/-- Check if a type variable occurs in a list of types -/
def occursInList (varId : Nat) : List MonoTy → Bool
  | [] => false
  | t :: rest => occursK varId t || occursInList varId rest

/-- Check if a type variable occurs in a type (kind-polymorphic occurs check) -/
def occursK (varId : Nat) : {k : Kind} → Ty k → Bool
  | _, .var v => v.id == varId
  | _, .starPrim _ => false
  | _, .higherPrim _ => false
  | _, .userCon _ _ => false
  | _, .app f a => occursK varId f || occursK varId a
  | _, .arrow from_ to => occursK varId from_ || occursK varId to
  | _, .tuple fst snd rest =>
    occursK varId fst || occursK varId snd || occursInList varId rest
end

/-- Monomorphic occurs check (for backwards compatibility) -/
def occurs (varId : Nat) (ty : MonoTy) : Bool := occursK varId ty

/-- Bind a type variable to a type of the same kind, with occurs check -/
def bindVarK {k : Kind} (v : TyVarId) (ty : Ty k) (ctx : UnifyContext) : UnifyResult :=
  -- If binding to itself, return empty substitution
  match ty with
  | .var v' =>
    if v.id == v'.id then
      .ok Subst.empty
    else if occursK v.id ty then
      -- For error message, we need a MonoTy - use a placeholder
      .error (.occursCheck v (.var ⟨s!"<kind {k}>", 0, .star⟩) ctx.actualSpan)
    else
      .ok (Subst.singletonAny v.id ⟨k, ty⟩)
  | _ =>
    if occursK v.id ty then
      .error (.occursCheck v (.var ⟨s!"<kind {k}>", 0, .star⟩) ctx.actualSpan)
    else
      .ok (Subst.singletonAny v.id ⟨k, ty⟩)

/-- Bind a monomorphic type variable -/
def bindVar (v : TyVarId) (ty : MonoTy) (ctx : UnifyContext) : UnifyResult :=
  bindVarK v ty ctx

mutual
  /-- Unify two monomorphic types (kind *) -/
  partial def unifyMono (t1 t2 : MonoTy) (ctx : UnifyContext) : UnifyResult := do
    -- Quick equality check
    if t1 == t2 then
      return Subst.empty

    match t1, t2 with
    | .var v1, .var v2 =>
      if v1.id == v2.id then
        return Subst.empty
      else
        -- Prefer binding the one with higher ID (todo: review)
        if v1.id > v2.id then
          bindVar v1 t2 ctx
        else
          bindVar v2 t1 ctx

    | .var v, t =>
      bindVar v t ctx

    | t, .var v =>
      bindVar v t ctx

    -- Primitive types
    | .starPrim p1, .starPrim p2 =>
      if p1 == p2 then
        return Subst.empty
      else
        .error (.typeMismatch t1 t2 ctx.purpose ctx.expectedSpan ctx.actualSpan)

    -- Type constructors
    | .userCon _ id1, .userCon _ id2 =>
      if id1 == id2 then
        return Subst.empty
      else
        .error (.typeMismatch t1 t2 ctx.purpose ctx.expectedSpan ctx.actualSpan)

    -- Function types
    | .arrow from1 to1, .arrow from2 to2 => do
      let σ1 ← unifyMono from1 from2 ctx
      let σ2 ← unifyMono (σ1.apply to1) (σ1.apply to2) ctx
      return σ2.compose σ1

    -- Type application
    | .app f1 a1, .app f2 a2 =>
      unifyAppSome ⟨_, f1⟩ ⟨_, a1⟩ ⟨_, f2⟩ ⟨_, a2⟩ ctx

    -- Tuple types
    | .tuple fst1 snd1 rest1, .tuple fst2 snd2 rest2 =>
      if rest1.length != rest2.length then
        .error (.typeMismatch t1 t2 ctx.purpose ctx.expectedSpan ctx.actualSpan)
      else do
        let σ1 ← unifyMono fst1 fst2 ctx
        let σ2 ← unifyMono (σ1.apply snd1) (σ1.apply snd2) ctx
        let σ12 := σ2.compose σ1
        unifyLists (rest1.map σ12.apply) (rest2.map σ12.apply) σ12 ctx

    -- Mismatch cases
    | _, _ =>
      .error (.typeMismatch t1 t2 ctx.purpose ctx.expectedSpan ctx.actualSpan)

  /-- Unify two SomeTy values (heterogeneous unification) -/
  partial def unifySome (s1 s2 : SomeTy) (ctx : UnifyContext) : UnifyResult := do
    -- First check if kinds match
    if h : s1.kind = s2.kind then
      -- Kinds match - use homogeneous unification
      let t2' : Ty s1.kind := h ▸ s2.ty
      unifyAtKind s1.kind s1.ty t2' ctx
    else
      .error (.typeMismatch (.var ⟨s!"kind {s1.kind}", 0, .star⟩) (.var ⟨s!"kind {s2.kind}", 0, .star⟩) ctx.purpose ctx.expectedSpan ctx.actualSpan)

  /-- Unify two types at a given kind -/
  partial def unifyAtKind (k : Kind) (t1 t2 : Ty k) (ctx : UnifyContext) : UnifyResult := do
    match k with
    | .star => unifyMono t1 t2 ctx
    | .arrow k1 k2 => unifyArrowK k1 k2 t1 t2 ctx

  /-- Unify two arrow-kinded types -/
  partial def unifyArrowK (k1 k2 : Kind) (t1 t2 : Ty (.arrow k1 k2)) (ctx : UnifyContext) : UnifyResult := do
    match t1, t2 with
    -- Both are type variables - bind one to the other
    | .var v1, .var v2 =>
      if v1.id == v2.id then
        return Subst.empty
      else if v1.id > v2.id then
        bindVarK v1 t2 ctx
      else
        bindVarK v2 t1 ctx

    -- One is a variable, bind it
    | .var v, t => bindVarK v t ctx
    | t, .var v => bindVarK v t ctx

    -- Both are higher primitives
    | .higherPrim p1, .higherPrim p2 =>
      if p1 == p2 then return Subst.empty
      else .error (.typeMismatch (.var ⟨s!"{p1}", 0, .star⟩) (.var ⟨s!"{p2}", 0, .star⟩) ctx.purpose ctx.expectedSpan ctx.actualSpan)

    -- Both are user-defined type constructors
    | .userCon _ id1, .userCon _ id2 =>
      if id1 == id2 then return Subst.empty
      else .error (.typeMismatch (.var ⟨id1.name, 0, .star⟩) (.var ⟨id2.name, 0, .star⟩) ctx.purpose ctx.expectedSpan ctx.actualSpan)

    -- Type application at arrow kind
    | .app f1 a1, .app f2 a2 =>
      unifyAppSome ⟨_, f1⟩ ⟨_, a1⟩ ⟨_, f2⟩ ⟨_, a2⟩ ctx

    -- Mismatch
    | _, _ =>
      .error (.typeMismatch (.var ⟨"_", 0, .star⟩) (.var ⟨"_", 0, .star⟩) ctx.purpose ctx.expectedSpan ctx.actualSpan)

  /-- Unify type applications using SomeTy to handle heterogeneous existential kinds -/
  partial def unifyAppSome (f1 a1 f2 a2 : SomeTy) (ctx : UnifyContext) : UnifyResult := do
    -- Unify the type constructors
    let σ1 ← unifySome f1 f2 ctx
    -- Apply substitution and unify arguments
    let a1' := σ1.applySome a1
    let a2' := σ1.applySome a2
    let σ2 ← unifySome a1' a2' ctx
    return σ2.compose σ1

  /-- Unify two arrays of monomorphic types element-wise -/
  partial def unifyArrays (arr1 arr2 : Array MonoTy) (ctx : UnifyContext) : UnifyResult := do
    let mut σ := Subst.empty
    for i in [:arr1.size] do
      if h : i < arr1.size ∧ i < arr2.size then
        let t1 := σ.apply arr1[i]
        let t2 := σ.apply arr2[i]
        let σ' ← unifyMono t1 t2 ctx
        σ := σ'.compose σ
    return σ

  /-- Unify two lists of monomorphic types element-wise, accumulating substitution -/
  partial def unifyLists (ts1 ts2 : List MonoTy) (acc : Subst) (ctx : UnifyContext) : UnifyResult := do
    match ts1, ts2 with
    | [], [] => return acc
    | t1 :: rest1, t2 :: rest2 =>
      let σ ← unifyMono t1 t2 ctx
      let acc' := σ.compose acc
      unifyLists (rest1.map acc'.apply) (rest2.map acc'.apply) acc' ctx
    | _, _ => return acc  -- Shouldn't happen if lengths match
end

/-- Simple unification with minimal context (for internal use) -/
def unify (t1 t2 : MonoTy) (span : Span) : UnifyResult :=
  unifyMono t1 t2 { purpose := .general, expectedSpan := span, actualSpan := span }

/-- Unify with purpose context -/
def unifyWith (expected actual : MonoTy) (purpose : UnifyPurpose)
    (expectedSpan actualSpan : Span) : UnifyResult :=
  unifyMono expected actual { purpose, expectedSpan, actualSpan }

/-- Unify a list of types to a single type -/
def unifyAll (types : Array MonoTy) (spans : Array Span) (purpose : UnifyPurpose)
    : Except InferError (MonoTy × Subst) := do
  -- Assert that spans and types arrays have the same length
  if types.size != spans.size then
    panic! s!"unifyAll: types.size ({types.size}) != spans.size ({spans.size})"

  match types[0]? with
  | none => return (.starPrim .unit, Subst.empty)
  | some first =>
    let firstSpan := spans[0]!
    let mut result := first
    let mut σ := Subst.empty
    for i in [1:types.size] do
      match types[i]? with
      | none => pure ()
      | some ty =>
        let tySpan := spans[i]!
        let ctx : UnifyContext := {
          purpose := purpose
          expectedSpan := firstSpan
          actualSpan := tySpan
        }
        let σ' ← unifyMono (σ.apply result) (σ.apply ty) ctx
        σ := σ'.compose σ
        result := σ.apply result
    return (result, σ)

end Unify

end Soma.Infer
