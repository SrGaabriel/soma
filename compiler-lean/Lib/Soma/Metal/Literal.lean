/-
  Soma.Metal.Literal
  Literal values in Metal IR.
-/
import Soma.Typing

namespace Soma.Metal

open Soma.Typing

/-- Literal values -/
inductive Literal where
  | int (value : Int)
  | bool (value : Bool)
  | string (value : String)
  deriving Repr, BEq, Inhabited

namespace Literal

/-- Get the type of a literal -/
def type : Literal → MonoTy
  | .int _ => Ty.int
  | .bool _ => Ty.bool
  | .string _ => Ty.string

/-- Pretty print a literal -/
def toString : Literal → String
  | .int n => s!"{n}"
  | .bool b => if b then "true" else "false"
  | .string s => s!"\"{s}\""

instance : ToString Literal := ⟨Literal.toString⟩

end Literal

end Soma.Metal
