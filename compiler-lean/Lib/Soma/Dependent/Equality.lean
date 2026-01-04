import Soma.Core.Value
import Soma.Core.Level
import Soma.Core.Eval
import Soma.Metal.Expr
import Soma.Dependent.Monad

namespace Soma.Dependent.Equality

open Soma.Core
open Soma.Metal (Expr Name BinderInfo)
open Soma.Syntax (Span)

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
  -- Create a proper closure that returns the output type
  let bodyTerm := Term.eq tyLevel (Term.var 1 "_ty") (Term.var 2 "_rhs") (Term.var 3 "_lhs")
  let env := Env.empty.extend "_ty" ty |>.extend "_lhs" lhs |>.extend "_rhs" rhs
  .vPi .omega .explicit "_eq" eqIn (Closure.term "_" env bodyTerm)

/-- The type of trans: {A : Type} -> {x y z : A} -> x = y -> y = z -> x = z -/
def transType (tyLevel : Level) (ty x y z : Value) : Value :=
  let eqXY := mkEq tyLevel ty x y
  -- (x = y) -> (y = z) -> (x = z)
  -- Outer closure returns the inner Pi type (constant)
  let outerBodyTerm := Term.pi .omega .explicit "_yz"
    (Term.eq tyLevel (Term.var 4 "_ty") (Term.var 2 "_y") (Term.var 1 "_z"))
    (Term.eq tyLevel (Term.var 5 "_ty") (Term.var 4 "_x") (Term.var 2 "_z"))
  let outerEnv := Env.empty.extend "_ty" ty |>.extend "_x" x |>.extend "_y" y |>.extend "_z" z
  .vPi .omega .explicit "_xy" eqXY (Closure.term "_" outerEnv outerBodyTerm)

/-- The type of cong: {A B : Type} -> (f : A -> B) -> {x y : A} -> x = y -> f x = f y -/
def congType (tyLevel : Level) (domTy codTy : Value) (f lhs rhs : Value) : Value :=
  let eqIn := mkEq tyLevel domTy lhs rhs
  -- Create a closure that returns the output equality type
  let bodyTerm := Term.eq tyLevel
    (Term.var 2 "_codTy")
    (Term.app (Term.var 3 "_f") [Term.var 4 "_lhs"])
    (Term.app (Term.var 3 "_f") [Term.var 4 "_rhs"])
  let env := Env.empty.extend "_codTy" codTy |>.extend "_f" f |>.extend "_lhs" lhs |>.extend "_rhs" rhs
  .vPi .omega .explicit "_eq" eqIn (Closure.term "_" env bodyTerm)

end Soma.Dependent.Equality
