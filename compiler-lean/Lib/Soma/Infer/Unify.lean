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

/-- Check if a type variable occurs in a type (kind-polymorphic occurs check) -/
def occursK (varId : Nat) : {k : Kind} → Ty k → Bool
  | _, .var v => v.id == varId
  | _, .starPrim _ => false
  | _, .higherPrim _ => false
  | _, .userCon _ _ => false
  | _, .app f a => occursK varId f || occursK varId a
  | _, .arrow from_ to => occursK varId from_ || occursK varId to
  | _, .tuple2 a b => occursK varId a || occursK varId b
  | _, .tuple3 a b c => occursK varId a || occursK varId b || occursK varId c
  | _, .tuple4 a b c d => occursK varId a || occursK varId b || occursK varId c || occursK varId d
  | _, .tuple5 a b c d e => occursK varId a || occursK varId b || occursK varId c || occursK varId d || occursK varId e
  | _, .tuple6 a b c d e f => occursK varId a || occursK varId b || occursK varId c || occursK varId d || occursK varId e || occursK varId f
  | _, .tuple7 a b c d e f g => occursK varId a || occursK varId b || occursK varId c || occursK varId d || occursK varId e || occursK varId f || occursK varId g
  | _, .tuple8 a b c d e f g h => occursK varId a || occursK varId b || occursK varId c || occursK varId d || occursK varId e || occursK varId f || occursK varId g || occursK varId h

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
    | .tuple2 a1 b1, .tuple2 a2 b2 => do
      let σ1 ← unifyMono a1 a2 ctx
      let σ2 ← unifyMono (σ1.apply b1) (σ1.apply b2) ctx
      return σ2.compose σ1

    | .tuple3 a1 b1 c1, .tuple3 a2 b2 c2 => do
      let σ1 ← unifyMono a1 a2 ctx
      let σ2 ← unifyMono (σ1.apply b1) (σ1.apply b2) ctx
      let σ3 ← unifyMono (σ2.apply (σ1.apply c1)) (σ2.apply (σ1.apply c2)) ctx
      return σ3.compose (σ2.compose σ1)

    | .tuple4 a1 b1 c1 d1, .tuple4 a2 b2 c2 d2 => do
      let σ1 ← unifyMono a1 a2 ctx
      let σ2 ← unifyMono (σ1.apply b1) (σ1.apply b2) ctx
      let σ12 := σ2.compose σ1
      let σ3 ← unifyMono (σ12.apply c1) (σ12.apply c2) ctx
      let σ123 := σ3.compose σ12
      let σ4 ← unifyMono (σ123.apply d1) (σ123.apply d2) ctx
      return σ4.compose σ123

    | .tuple5 a1 b1 c1 d1 e1, .tuple5 a2 b2 c2 d2 e2 => do
      let σ1 ← unifyMono a1 a2 ctx
      let σ2 ← unifyMono (σ1.apply b1) (σ1.apply b2) ctx
      let σ12 := σ2.compose σ1
      let σ3 ← unifyMono (σ12.apply c1) (σ12.apply c2) ctx
      let σ123 := σ3.compose σ12
      let σ4 ← unifyMono (σ123.apply d1) (σ123.apply d2) ctx
      let σ1234 := σ4.compose σ123
      let σ5 ← unifyMono (σ1234.apply e1) (σ1234.apply e2) ctx
      return σ5.compose σ1234

    | .tuple6 a1 b1 c1 d1 e1 f1, .tuple6 a2 b2 c2 d2 e2 f2 => do
      let σ1 ← unifyMono a1 a2 ctx
      let σ2 ← unifyMono (σ1.apply b1) (σ1.apply b2) ctx
      let σ12 := σ2.compose σ1
      let σ3 ← unifyMono (σ12.apply c1) (σ12.apply c2) ctx
      let σ123 := σ3.compose σ12
      let σ4 ← unifyMono (σ123.apply d1) (σ123.apply d2) ctx
      let σ1234 := σ4.compose σ123
      let σ5 ← unifyMono (σ1234.apply e1) (σ1234.apply e2) ctx
      let σ12345 := σ5.compose σ1234
      let σ6 ← unifyMono (σ12345.apply f1) (σ12345.apply f2) ctx
      return σ6.compose σ12345

    | .tuple7 a1 b1 c1 d1 e1 f1 g1, .tuple7 a2 b2 c2 d2 e2 f2 g2 => do
      let σ1 ← unifyMono a1 a2 ctx
      let σ2 ← unifyMono (σ1.apply b1) (σ1.apply b2) ctx
      let σ12 := σ2.compose σ1
      let σ3 ← unifyMono (σ12.apply c1) (σ12.apply c2) ctx
      let σ123 := σ3.compose σ12
      let σ4 ← unifyMono (σ123.apply d1) (σ123.apply d2) ctx
      let σ1234 := σ4.compose σ123
      let σ5 ← unifyMono (σ1234.apply e1) (σ1234.apply e2) ctx
      let σ12345 := σ5.compose σ1234
      let σ6 ← unifyMono (σ12345.apply f1) (σ12345.apply f2) ctx
      let σ123456 := σ6.compose σ12345
      let σ7 ← unifyMono (σ123456.apply g1) (σ123456.apply g2) ctx
      return σ7.compose σ123456

    | .tuple8 a1 b1 c1 d1 e1 f1 g1 h1, .tuple8 a2 b2 c2 d2 e2 f2 g2 h2 => do
      let σ1 ← unifyMono a1 a2 ctx
      let σ2 ← unifyMono (σ1.apply b1) (σ1.apply b2) ctx
      let σ12 := σ2.compose σ1
      let σ3 ← unifyMono (σ12.apply c1) (σ12.apply c2) ctx
      let σ123 := σ3.compose σ12
      let σ4 ← unifyMono (σ123.apply d1) (σ123.apply d2) ctx
      let σ1234 := σ4.compose σ123
      let σ5 ← unifyMono (σ1234.apply e1) (σ1234.apply e2) ctx
      let σ12345 := σ5.compose σ1234
      let σ6 ← unifyMono (σ12345.apply f1) (σ12345.apply f2) ctx
      let σ123456 := σ6.compose σ12345
      let σ7 ← unifyMono (σ123456.apply g1) (σ123456.apply g2) ctx
      let σ1234567 := σ7.compose σ123456
      let σ8 ← unifyMono (σ1234567.apply h1) (σ1234567.apply h2) ctx
      return σ8.compose σ1234567

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
