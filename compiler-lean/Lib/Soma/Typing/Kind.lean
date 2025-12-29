namespace Soma.Typing

/-- Kinds classify types -/
inductive Kind where
  | star                              -- Types (kind *)
  | row                               -- Row types (for record polymorphism)
  | label                             -- Field labels
  | arrow (from_ : Kind) (to : Kind)  -- Type constructors
  deriving Repr, BEq, Hashable, Inhabited, DecidableEq

namespace Kind

/-- Pretty print a kind -/
def toString : Kind → String
  | .star => "*"
  | .row => "Row"
  | .label => "Label"
  | .arrow from_ to => s!"({from_.toString} -> {to.toString})"

instance : ToString Kind := ⟨Kind.toString⟩

/-- Construct an n-ary arrow kind: * -> * -> ... -> * -/
def nary (n : Nat) : Kind :=
  match n with
  | 0 => .star
  | n + 1 => .arrow .star (nary n)

/-- Count the arity of a kind (number of arrows before reaching *) -/
def arity : Kind → Nat
  | .star => 0
  | .row => 0
  | .label => 0
  | .arrow _ to => 1 + arity to

/-- Get the result kind after applying n arguments -/
def resultAfter (k : Kind) (n : Nat) : Option Kind :=
  match n, k with
  | 0, k => some k
  | _ + 1, .arrow _ to => resultAfter to (n - 1)
  | _ + 1, .star => none
  | _ + 1, .row => none
  | _ + 1, .label => none

/-- Parse a kind name string into a Kind -/
def fromString (name : String) : Kind :=
  match name with
  | "*" => .star
  | "%" | "Row" => .row
  | "#" | "Label" => .label
  | _ => .star -- Default to star for unknown kinds (todo: also support arrow kinds)

end Kind

end Soma.Typing
