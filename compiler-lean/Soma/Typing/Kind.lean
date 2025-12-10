namespace Soma.Typing

/-- Kinds classify types -/
inductive Kind where
  | star
  | arrow (from_ : Kind) (to : Kind)
  deriving Repr, BEq, Hashable, Inhabited, DecidableEq

namespace Kind

/-- Pretty print a kind -/
def toString : Kind → String
  | .star => "*"
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
  | .arrow _ to => 1 + arity to

/-- Get the result kind after applying n arguments -/
def resultAfter (k : Kind) (n : Nat) : Option Kind :=
  match n, k with
  | 0, k => some k
  | _ + 1, .arrow _ to => resultAfter to (n - 1)
  | _ + 1, .star => none

end Kind

end Soma.Typing
