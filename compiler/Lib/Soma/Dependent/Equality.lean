import Soma.Core.Value
import Soma.Core.Level
import Soma.Core.Eval
import Soma.Core.Expr
import Soma.Dependent.Monad

namespace Soma.Dependent.Equality

open Soma.Core

/-- Create an equality value: x = y : A -/
def mkEq (tyLevel : Level) (ty lhs rhs : Value) : Value :=
  .vEq tyLevel ty lhs rhs

/-- Create a reflexivity proof: refl : x = x -/
def mkRefl (ty x : Value) : Value :=
  .vRefl ty x

/-- Create a transport value: transport P eq px -/
def mkTransport (tyLevel : Level) (ty motive lhs rhs eq body : Value) : Value :=
  .vTransport tyLevel ty motive lhs rhs eq body

/-! ## Derived Combinators (as Value constructors)

These combinators are derived from transport. They show how the standard
equality operations can be defined from the J eliminator.

Ideally, these would be:

  symm : {A : Type} -> {x y : A} -> x = y -> y = x
  symm {A} {x} {y} eq = transport (fun z => z = x) eq refl

  trans : {A : Type} -> {x y z : A} -> x = y -> y = z -> x = z
  trans {A} {x} {y} {z} xy yz = transport (fun w => x = w) yz xy

  cong : {A B : Type} -> (f : A -> B) -> {x y : A} -> x = y -> f x = f y
  cong f eq = transport (fun z => f x = f z) eq refl
-/

/-- Apply symmetry to an equality proof.
    symm : x = y -> y = x
-/
def applySymm (tyLevel : Level) (ty lhs rhs eq : Value) : Value :=
  -- Motive: λz. z = lhs
  -- This is represented as a stuck application since we need a closure
  -- The body is refl : lhs = lhs
  let body := mkRefl ty lhs
  -- Transport P eq body where P z = (z = lhs)
  -- When eq : lhs = rhs, transport gives us rhs = lhs
  mkTransport tyLevel ty (.vLabelLit "_symm_motive") lhs rhs eq body

/-- Apply transitivity to two equality proofs -/
def applyTrans (tyLevel : Level) (ty _x y z xy yz : Value) : Value :=
  -- Transport (λw. x = w) yz xy
  -- xy : x = y, yz : y = z, result : x = z
  mkTransport tyLevel ty (.vLabelLit "_trans_motive") y z yz xy

/-- Apply congruence to an equality proof -/
def applyCong (tyLevel : Level) (domTy codTy : Value) (_f lhs rhs eq : Value) : Value :=
  -- We need f lhs and f rhs
  let fLhs := Value.vNeutral codTy (.nApp (.nVar ⟨"_f", ⟨0⟩⟩) lhs)
  let _fRhs := Value.vNeutral codTy (.nApp (.nVar ⟨"_f", ⟨0⟩⟩) rhs)
  -- body is refl : f lhs = f lhs
  let body := mkRefl codTy fLhs
  -- Transport along eq to get f lhs = f rhs
  mkTransport tyLevel domTy (.vLabelLit "_cong_motive") lhs rhs eq body

/-- The type of symm: {A : Type} -> {x y : A} -> x = y -> y = x -/
def symmType (tyLevel : Level) (ty lhs rhs : Value) : Value :=
  -- (x = y) -> (y = x)
  let eqIn := mkEq tyLevel ty lhs rhs
  -- Env: _ty(lvl 0), _lhs(lvl 1), _rhs(lvl 2). Closure param _eq(lvl 3). Size=4.
  -- bvar 3=_ty, bvar 2=_lhs, bvar 1=_rhs, bvar 0=_eq
  -- Body: Eq tyLevel _ty _rhs _lhs = rhs = lhs = y = x
  let bodyExpr := Soma.Core.Expr.eqTy tyLevel (.bvar 3) (.bvar 1) (.bvar 2)
  let env := Env.empty.extend "_ty" ty |>.extend "_lhs" lhs |>.extend "_rhs" rhs
  .vPi .omega .explicit "_eq" eqIn (Closure.term "_" env bodyExpr)

/-- The type of trans: {A : Type} -> {x y z : A} -> x = y -> y = z -> x = z -/
def transType (tyLevel : Level) (ty x y z : Value) : Value :=
  let eqXY := mkEq tyLevel ty x y
  -- (x = y) -> (y = z) -> (x = z)
  -- Outer closure body: Pi omega explicit "_yz" (Eq ty y z) (Eq ty x z)
  -- Env has: _ty(0), _x(1), _y(2), _z(3), then closure param at 4
  -- Inner bvar indices: _ty=4, _x=3, _y=2, _z=1, _xy(closure param)=0
  -- After closure application, inner Pi's body has _yz at 0
  -- So: domain = Eq (bvar 4=_ty) (bvar 2=_y) (bvar 1=_z)
  --     codomain = Eq (bvar 5=_ty) (bvar 4=_x) (bvar 2=_z)
  let outerBodyExpr := Soma.Core.Expr.pi .omega .explicit "_yz"
    (Soma.Core.Expr.eqTy tyLevel (.bvar 4) (.bvar 2) (.bvar 1))
    (Soma.Core.Expr.eqTy tyLevel (.bvar 5) (.bvar 4) (.bvar 2))
  let outerEnv := Env.empty.extend "_ty" ty |>.extend "_x" x |>.extend "_y" y |>.extend "_z" z
  .vPi .omega .explicit "_xy" eqXY (Closure.term "_" outerEnv outerBodyExpr)

/-- The type of cong: {A B : Type} -> (f : A -> B) -> {x y : A} -> x = y -> f x = f y -/
def congType (tyLevel : Level) (domTy codTy : Value) (f lhs rhs : Value) : Value :=
  let eqIn := mkEq tyLevel domTy lhs rhs
  -- Env: _codTy(lvl 0), _f(lvl 1), _lhs(lvl 2), _rhs(lvl 3). Size=4.
  -- Closure param _eq(lvl 4). Size=5.
  -- bvar 4=_codTy, bvar 3=_f, bvar 2=_lhs, bvar 1=_rhs, bvar 0=_eq
  -- Body: Eq tyLevel codTy (f lhs) (f rhs)
  let bodyExpr := Soma.Core.Expr.eqTy tyLevel
    (.bvar 4)
    (.app (.bvar 3) (.bvar 2))
    (.app (.bvar 3) (.bvar 1))
  let env := Env.empty.extend "_codTy" codTy |>.extend "_f" f |>.extend "_lhs" lhs |>.extend "_rhs" rhs
  .vPi .omega .explicit "_eq" eqIn (Closure.term "_" env bodyExpr)

end Soma.Dependent.Equality
