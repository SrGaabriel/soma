import Kenosis

namespace Soma.Core

open Kenosis

/-- Literal values -/
inductive Literal where
  | int (value : Int)
  | float (value : Float)
  | bool (value : Bool)
  | string (value : String)
  deriving Repr, BEq, Inhabited, Serialize, Deserialize

namespace Literal

/-- Pretty print a literal -/
def toString : Literal → String
  | .int n => s!"{n}"
  | .float f => s!"{f}"
  | .bool b => if b then "true" else "false"
  | .string s => s!"\"{s}\""

instance : ToString Literal := ⟨Literal.toString⟩

end Literal

end Soma.Core
