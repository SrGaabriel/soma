import Soma.Core.Value
import Soma.Core.Level
import Soma.Core.Eval
import Soma.Core.Expr
import Soma.Dependent.Monad

namespace Soma.Dependent.Equality

open Soma.Core

/-- Build the equality type `lhs =[ty] rhs` -/
def mkEq (eqId : Unique) (ty lhs rhs : Value) : Value :=
  .vDataType eqId [ty, lhs, rhs]

/-- Create a reflexivity proof -/
def mkRefl (eqId : Unique) (refl : QualifiedName × Nat) (ty x : Value) : Value :=
  let (reflName, reflTag) := refl
  let resultTy : Value := .vDataType eqId [ty, x, x]
  .vConstructor reflName reflTag [ty, x] resultTy

end Soma.Dependent.Equality
