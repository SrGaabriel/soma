/-
  Soma.Metal.Literal
  Literal values in Metal IR.
-/

namespace Soma.Metal

/-- Literal values -/
inductive Literal where
  | int (value : Int)
  | bool (value : Bool)
  | string (value : String)
  deriving Repr, BEq, Inhabited

namespace Literal

/-- Pretty print a literal -/
def toString : Literal → String
  | .int n => s!"{n}"
  | .bool b => if b then "true" else "false"
  | .string s => s!"\"{s}\""

instance : ToString Literal := ⟨Literal.toString⟩

end Literal

end Soma.Metal
