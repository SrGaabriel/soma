import Kenosis

namespace Soma.Core

open Kenosis

/-- Quantities for QTT: how many times a variable may be used -/
inductive Quantity where
  /-- Erased: not present at runtime (type-level only) -/
  | zero
  /-- Linear: used exactly once -/
  | one
  /-- Unrestricted: may be used any number of times -/
  | omega
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited, Serialize, Deserialize

namespace Quantity

instance : ToString Quantity where
  toString
    | .zero => "0"
    | .one => "1"
    | .omega => "ω"

/-- Display with descriptive name -/
def displayName : Quantity → String
  | .zero => "erased"
  | .one => "linear"
  | .omega => "unrestricted"

/-- Addition of quantities (how many times is x used total?)
    0 + q = q
    1 + 1 = ω
    ω + _ = ω
-/
def add : Quantity → Quantity → Quantity
  | .zero, q => q
  | q, .zero => q
  | .one, .one => .omega
  | .omega, _ => .omega
  | _, .omega => .omega

instance : Add Quantity := ⟨add⟩

/-- Multiplication of quantities (if f uses x q₁ times and we call f q₂ times...)
    0 · q = 0
    1 · q = q
    ω · ω = ω
-/
def mul : Quantity → Quantity → Quantity
  | .zero, _ => .zero
  | _, .zero => .zero
  | .one, q => q
  | q, .one => q
  | .omega, .omega => .omega

instance : Mul Quantity := ⟨mul⟩

/-- Ordering: 0 ≤ 1 ≤ ω
    A quantity q₁ is less than or equal to q₂ if using q₁ times
    is permitted when q₂ times is allowed.
-/
def le : Quantity → Quantity → Bool
  | .zero, _ => true
  | .one, .one => true
  | .one, .omega => true
  | .omega, .omega => true
  | _, _ => false

instance : LE Quantity := ⟨fun q1 q2 => q1.le q2⟩

instance : DecidableRel (α := Quantity) (· ≤ ·) := fun q1 q2 =>
  if h : q1.le q2 then isTrue h else isFalse h

/-- Strict ordering -/
def lt : Quantity → Quantity → Bool
  | .zero, .one => true
  | .zero, .omega => true
  | .one, .omega => true
  | _, _ => false

instance : LT Quantity := ⟨fun q1 q2 => q1.lt q2⟩

instance : DecidableRel (α := Quantity) (· < ·) := fun q1 q2 =>
  if h : q1.lt q2 then isTrue h else isFalse h

/-- Zero is the additive identity -/
theorem add_zero (q : Quantity) : q + .zero = q := by
  cases q <;> rfl

theorem zero_add (q : Quantity) : .zero + q = q := by
  cases q <;> rfl

/-- One is the multiplicative identity -/
theorem mul_one (q : Quantity) : q * .one = q := by
  cases q <;> rfl

theorem one_mul (q : Quantity) : .one * q = q := by
  cases q <;> rfl

/-- Zero annihilates multiplication -/
theorem mul_zero (q : Quantity) : q * .zero = .zero := by
  cases q <;> rfl

theorem zero_mul (q : Quantity) : .zero * q = .zero := by
  cases q <;> rfl

/-- Addition is commutative -/
theorem add_comm (q1 q2 : Quantity) : q1 + q2 = q2 + q1 := by
  cases q1 <;> cases q2 <;> rfl

/-- Multiplication is commutative -/
theorem mul_comm (q1 q2 : Quantity) : q1 * q2 = q2 * q1 := by
  cases q1 <;> cases q2 <;> rfl

/-- Addition is associative -/
theorem add_assoc (q1 q2 q3 : Quantity) : (q1 + q2) + q3 = q1 + (q2 + q3) := by
  cases q1 <;> cases q2 <;> cases q3 <;> rfl

/-- Multiplication is associative -/
theorem mul_assoc (q1 q2 q3 : Quantity) : (q1 * q2) * q3 = q1 * (q2 * q3) := by
  cases q1 <;> cases q2 <;> cases q3 <;> rfl

/-- Multiplication distributes over addition -/
theorem mul_add (q1 q2 q3 : Quantity) : q1 * (q2 + q3) = q1 * q2 + q1 * q3 := by
  cases q1 <;> cases q2 <;> cases q3 <;> rfl

theorem add_mul (q1 q2 q3 : Quantity) : (q1 + q2) * q3 = q1 * q3 + q2 * q3 := by
  cases q1 <;> cases q2 <;> cases q3 <;> rfl

/-! ## Ordering Laws -/

/-- Ordering is reflexive -/
theorem le_refl (q : Quantity) : q ≤ q := by
  cases q <;> decide

/-- Ordering is transitive -/
theorem le_trans {q1 q2 q3 : Quantity} (h1 : q1 ≤ q2) (h2 : q2 ≤ q3) : q1 ≤ q3 := by
  cases q1 <;> cases q2 <;> cases q3 <;> simp_all [LE.le, le]

/-- Ordering is antisymmetric -/
theorem le_antisymm {q1 q2 : Quantity} (h1 : q1 ≤ q2) (h2 : q2 ≤ q1) : q1 = q2 := by
  cases q1 <;> cases q2 <;> simp_all [LE.le, le]

/-- Check if a quantity is erased (zero) -/
def isErased : Quantity → Bool
  | .zero => true
  | _ => false

/-- Check if a quantity is linear (one) -/
def isLinear : Quantity → Bool
  | .one => true
  | _ => false

/-- Check if a quantity is unrestricted (omega) -/
def isUnrestricted : Quantity → Bool
  | .omega => true
  | _ => false

/-- Check if a quantity allows usage (non-zero) -/
def allowsUsage : Quantity → Bool
  | .zero => false
  | _ => true

/-- Check if a quantity allows duplication (not linear) -/
def allowsDuplication : Quantity → Bool
  | .one => false
  | _ => true

/-- Join (least upper bound) of two quantities -/
def join : Quantity → Quantity → Quantity
  | .omega, _ => .omega
  | _, .omega => .omega
  | .one, _ => .one
  | _, .one => .one
  | .zero, .zero => .zero

/-- Meet (greatest lower bound) of two quantities -/
def meet : Quantity → Quantity → Quantity
  | .zero, _ => .zero
  | _, .zero => .zero
  | .one, .one => .one
  | .one, .omega => .one
  | .omega, .one => .one
  | .omega, .omega => .omega

/-- The default quantity for user code (unrestricted) -/
def default : Quantity := .omega

/-- Scale a quantity: multiply by another quantity -/
def scale (q1 q2 : Quantity) : Quantity := q1 * q2

end Quantity

end Soma.Core
