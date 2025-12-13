/-
  Type Unification

  Key improvements over the old Haskell design:
  1. Kind-aware unification: checks kinds match before unifying
  2. Uses Except monad for clean error handling
  3. Proper occurs check with clear error messages
  4. Unification purpose tracking for better error context
-/

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

/-- Check if a type variable occurs in a type (occurs check) -/
def occurs (varId : Nat) (ty : MonoTy) : Bool :=
  ty.freeVars.any (·.id == varId)

/-- Bind a type variable to a type, checking for occurs -/
def bindVar (v : TyVarId) (ty : MonoTy) (ctx : UnifyContext) : UnifyResult :=
  -- If binding to itself, return empty substitution
  match ty with
  | .var v' =>
    if v.id == v'.id then
      .ok Subst.empty
    else if occurs v.id ty then
      .error (.occursCheck v ty ctx.actualSpan)
    else
      .ok (Subst.fromVar v ty)
  | _ =>
    -- Occurs check
    if occurs v.id ty then
      .error (.occursCheck v ty ctx.actualSpan)
    else
      .ok (Subst.fromVar v ty)

/-- Unify two monomorphic types -/
partial def unifyMono (t1 t2 : MonoTy) (ctx : UnifyContext) : UnifyResult := do
  -- Quick equality check
  if t1 == t2 then
    return Subst.empty

  match t1, t2 with
  -- Type variable cases
  | .var v1, .var v2 =>
    if v1.id == v2.id then
      return Subst.empty
    else
      -- Prefer binding the one with higher ID (arbitrary but consistent)
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
  | .con id1, .con id2 =>
    if id1 == id2 then
      return Subst.empty
    else
      .error (.typeMismatch t1 t2 ctx.purpose ctx.expectedSpan ctx.actualSpan)

  -- Function types
  | .arrow from1 to1, .arrow from2 to2 => do
    let σ1 ← unifyMono from1 from2 ctx
    let σ2 ← unifyMono (σ1.apply to1) (σ1.apply to2) ctx
    return σ2.compose σ1

  -- Type application - handle the common case: App (Ty (.arrow .star .star)) (Ty .star)
  -- Since we're unifying MonoTy (= Ty .star), and .app : Ty (.arrow k1 k2) → Ty k1 → Ty k2,
  -- we know k2 = .star. For the common case (Array, Ref, IO), k1 = .star too.
  | .app f1 a1, .app f2 a2 =>
    -- Check that the type constructors match
    -- We handle only the common case where both are higher primitives with star->star kind
    match f1, f2 with
    | .higherPrim p1, .higherPrim p2 =>
      if p1 == p2 then
        -- Same type constructor (like Array), unify the arguments
        -- Since higherPrim : Ty (.arrow .star .star), we know a1, a2 : Ty .star = MonoTy
        unifyMono a1 a2 ctx
      else
        .error (.typeMismatch t1 t2 ctx.purpose ctx.expectedSpan ctx.actualSpan)
    | _, _ =>
      -- For other cases (type variables, nested applications), we can't easily unify
      -- without full higher-kinded type support
      .error (.typeMismatch t1 t2 ctx.purpose ctx.expectedSpan ctx.actualSpan)

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
  match types[0]? with
  | none => return (.starPrim .unit, Subst.empty)
  | some first =>
    let firstSpan := spans[0]?.getD Span.uninhabited
    let mut result := first
    let mut σ := Subst.empty
    for i in [1:types.size] do
      match types[i]? with
      | none => pure ()
      | some ty =>
        let tySpan := spans[i]?.getD Span.uninhabited
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
