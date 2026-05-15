import Std.Data.HashMap
import Kenosis

namespace Soma.Core

open Kenosis

/-- Unique identifier for a level variable -/
structure LevelVarId where
  id : Nat
  name : String := ""
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited, Serialize, Deserialize

namespace LevelVarId

instance : ToString LevelVarId where
  toString v := if v.name.isEmpty then s!"u{v.id}" else v.name

end LevelVarId

/-- Universe levels -/
inductive Level where
  /-- Proposition universe: `Prop` -/
  | prop
  /-- Concrete level: Type₀, Type₁, etc. -/
  | lit (n : Nat)
  /-- Level variable for polymorphism -/
  | var (id : LevelVarId)
  /-- Maximum of two levels -/
  | max (l1 l2 : Level)
  /-- Successor level (l + 1) -/
  | succ (l : Level)
  deriving Repr, BEq, Hashable, Inhabited, Serialize, Deserialize

namespace Level

/-- Type₀ (the base universe) -/
def zero : Level := .lit 0

/-- Type₁ -/
def one : Level := .lit 1

/-- Is this level the `Prop` universe? -/
def isProp : Level → Bool
  | .prop => true
  | _ => false

/-- Add n to a level -/
def addLit (l : Level) (n : Nat) : Level :=
  match n with
  | 0 => l
  | n + 1 => .succ (addLit l n)

instance : HAdd Level Nat Level := ⟨addLit⟩

/-- Maximum of two levels with simplification -/
def mkMax (l1 l2 : Level) : Level :=
  match l1, l2 with
  | .prop, l => l
  | l, .prop => l
  | .lit n1, .lit n2 => .lit (Nat.max n1 n2)
  | l, .lit 0 => l
  | .lit 0, l => l
  | l1, l2 => if l1 == l2 then l1 else .max l1 l2

/-- Successor with simplification -/
def mkSucc (l : Level) : Level :=
  match l with
  | .prop => .lit 0
  | .lit n => .lit (n + 1)
  | l => .succ l

/-- Simplify a level expression -/
partial def simplify : Level → Level
  | .prop => .prop
  | .lit n => .lit n
  | .var id => .var id
  | .succ l =>
    match simplify l with
    | .prop => .lit 0
    | .lit n => .lit (n + 1)
    | l' => .succ l'
  | .max l1 l2 =>
    match simplify l1, simplify l2 with
    | .prop, l' => l'
    | l', .prop => l'
    | .lit n1, .lit n2 => .lit (Nat.max n1 n2)
    | l1', .lit 0 => l1'
    | .lit 0, l2' => l2'
    | l1', l2' => if l1' == l2' then l1' else .max l1' l2'

/-- Substitute a level variable with a level -/
def subst (l : Level) (id : LevelVarId) (replacement : Level) : Level :=
  match l with
  | .prop => .prop
  | .lit n => .lit n
  | .var v => if v == id then replacement else .var v
  | .max l1 l2 => mkMax (subst l1 id replacement) (subst l2 id replacement)
  | .succ l' => mkSucc (subst l' id replacement)

/-- Substitute multiple level variables -/
def substMap (l : Level) (σ : Std.HashMap LevelVarId Level) : Level :=
  match l with
  | .prop => .prop
  | .lit n => .lit n
  | .var v =>
    match σ.get? v with
    | some l' => l'
    | none => .var v
  | .max l1 l2 => mkMax (substMap l1 σ) (substMap l2 σ)
  | .succ l' => mkSucc (substMap l' σ)

/-- Check if level contains variables -/
def hasVars : Level → Bool
  | .prop => false
  | .lit _ => false
  | .var _ => true
  | .max l1 l2 => hasVars l1 || hasVars l2
  | .succ l => hasVars l

/-- Get all level variables -/
def freeVars : Level → List LevelVarId
  | .prop => []
  | .lit _ => []
  | .var v => [v]
  | .max l1 l2 => freeVars l1 ++ freeVars l2
  | .succ l => freeVars l

  -- Can't decide, assume false

/-- Convert level to subscript string -/
def toSubscript (l : Level) : String :=
  let rec natToSubscript (n : Nat) : String :=
    if n < 10 then
      String.singleton (Char.ofNat (0x2080 + n))  -- ₀₁₂₃₄₅₆₇₈₉
    else
      natToSubscript (n / 10) ++ natToSubscript (n % 10)
  match l with
  | .prop => "ₚ"
  | .lit n => natToSubscript n
  | .var v => s!"_{v}"
  | .max l1 l2 => s!"max({toSubscript l1},{toSubscript l2})"
  | .succ l' => s!"({toSubscript l'}+1)"

/-- Convert level to string -/
partial def toStringAux : Level → String
  | .prop => "Prop"
  | .lit 0 => "0"
  | .lit n => toString n
  | .var v => toString v
  | .max l1 l2 => s!"max({toStringAux l1}, {toStringAux l2})"
  | .succ l' => s!"({toStringAux l'} + 1)"

instance : ToString Level where
  toString := toStringAux

/-- A constraint on levels -/
inductive LevelConstraint where
  /-- l1 = l2 -/
  | eq (l1 l2 : Level)
  /-- l1 ≤ l2 -/
  | le (l1 l2 : Level)
  /-- result = max(l1, l2) -/
  | maxEq (l1 l2 result : Level)
  deriving Repr, BEq

namespace LevelConstraint

instance : ToString LevelConstraint where
  toString
    | .eq l1 l2 => s!"{l1} = {l2}"
    | .le l1 l2 => s!"{l1} ≤ {l2}"
    | .maxEq l1 l2 r => s!"max({l1}, {l2}) = {r}"

end LevelConstraint

end Level

end Soma.Core
