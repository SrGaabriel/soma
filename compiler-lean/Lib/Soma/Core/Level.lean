import Std.Data.HashMap
import Lean.Data.Json

namespace Soma.Core

/-- Unique identifier for a level variable -/
structure LevelVarId where
  id : Nat
  name : String := ""
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited

instance : Lean.ToJson LevelVarId where
  toJson v := .mkObj [("id", .num v.id), ("name", .str v.name)]

instance : Lean.FromJson LevelVarId where
  fromJson? j := do
    let id ← j.getObjValAs? Nat "id"
    let name ← j.getObjValAs? String "name"
    pure ⟨id, name⟩

namespace LevelVarId

instance : ToString LevelVarId where
  toString v := if v.name.isEmpty then s!"u{v.id}" else v.name

end LevelVarId

/-- Universe levels -/
inductive Level where
  /-- Concrete level: Type₀, Type₁, etc. -/
  | lit (n : Nat)
  /-- Level variable for polymorphism -/
  | var (id : LevelVarId)
  /-- Maximum of two levels -/
  | max (l1 l2 : Level)
  /-- Successor level (l + 1) -/
  | succ (l : Level)
  deriving Repr, BEq, Hashable, Inhabited

partial def Level.toJson : Level → Lean.Json
  | .lit n => .mkObj [("lit", .num n)]
  | .var v => .mkObj [("var", Lean.ToJson.toJson v)]
  | .max l1 l2 => .mkObj [("max", .arr #[l1.toJson, l2.toJson])]
  | .succ l => .mkObj [("succ", l.toJson)]

instance : Lean.ToJson Level where
  toJson := Level.toJson

partial def Level.fromJson? (j : Lean.Json) : Except String Level := do
  match j.getObjValAs? Nat "lit" with
  | .ok n => pure (.lit n)
  | .error _ =>
    match j.getObjVal? "var" with
    | .ok varJ =>
      let v ← Lean.FromJson.fromJson? varJ
      pure (.var v)
    | .error _ =>
      match j.getObjVal? "max" with
      | .ok (.arr arr) =>
        if arr.size = 2 then
          let l1 ← Level.fromJson? arr[0]!
          let l2 ← Level.fromJson? arr[1]!
          pure (.max l1 l2)
        else .error "Invalid max level: expected 2 elements"
      | _ =>
        match j.getObjVal? "succ" with
        | .ok succJ =>
          let l ← Level.fromJson? succJ
          pure (.succ l)
        | .error _ => .error s!"Unknown level JSON: {j}"

instance : Lean.FromJson Level where
  fromJson? := Level.fromJson?

namespace Level

/-! ## Common Levels -/

/-- Type₀ (the base universe) -/
def zero : Level := .lit 0

/-- Type₁ -/
def one : Level := .lit 1

/-- Type₂ -/
def two : Level := .lit 2

/-- Add n to a level -/
def addLit (l : Level) (n : Nat) : Level :=
  match n with
  | 0 => l
  | n + 1 => .succ (addLit l n)

instance : HAdd Level Nat Level := ⟨addLit⟩

/-- Maximum of two levels with simplification -/
def mkMax (l1 l2 : Level) : Level :=
  match l1, l2 with
  | .lit n1, .lit n2 => .lit (Nat.max n1 n2)
  | l, .lit 0 => l
  | .lit 0, l => l
  | l1, l2 => if l1 == l2 then l1 else .max l1 l2

/-- Successor with simplification -/
def mkSucc (l : Level) : Level :=
  match l with
  | .lit n => .lit (n + 1)
  | l => .succ l

/-- Simplify a level expression -/
partial def simplify : Level → Level
  | .lit n => .lit n
  | .var id => .var id
  | .succ l =>
    match simplify l with
    | .lit n => .lit (n + 1)
    | l' => .succ l'
  | .max l1 l2 =>
    match simplify l1, simplify l2 with
    | .lit n1, .lit n2 => .lit (Nat.max n1 n2)
    | l1', .lit 0 => l1'
    | .lit 0, l2' => l2'
    | l1', l2' => if l1' == l2' then l1' else .max l1' l2'

/-- Substitute a level variable with a level -/
def subst (l : Level) (id : LevelVarId) (replacement : Level) : Level :=
  match l with
  | .lit n => .lit n
  | .var v => if v == id then replacement else .var v
  | .max l1 l2 => mkMax (subst l1 id replacement) (subst l2 id replacement)
  | .succ l' => mkSucc (subst l' id replacement)

/-- Substitute multiple level variables -/
def substMap (l : Level) (σ : Std.HashMap LevelVarId Level) : Level :=
  match l with
  | .lit n => .lit n
  | .var v =>
    match σ.get? v with
    | some l' => l'
    | none => .var v
  | .max l1 l2 => mkMax (substMap l1 σ) (substMap l2 σ)
  | .succ l' => mkSucc (substMap l' σ)

/-- Check if level is a concrete literal -/
def isLit : Level → Bool
  | .lit _ => true
  | _ => false

/-- Try to get literal value -/
def toLit? : Level → Option Nat
  | .lit n => some n
  | _ => none

/-- Check if level contains variables -/
def hasVars : Level → Bool
  | .lit _ => false
  | .var _ => true
  | .max l1 l2 => hasVars l1 || hasVars l2
  | .succ l => hasVars l

/-- Get all level variables -/
def freeVars : Level → List LevelVarId
  | .lit _ => []
  | .var v => [v]
  | .max l1 l2 => freeVars l1 ++ freeVars l2
  | .succ l => freeVars l

/-- Get unique level variables -/
def freeVarsUnique (l : Level) : List LevelVarId :=
  let vars := l.freeVars
  vars.foldl (fun acc v => if acc.any (· == v) then acc else v :: acc) [] |>.reverse

/-- Compare two concrete levels -/
def leLit? (l1 l2 : Level) : Option Bool :=
  match l1.simplify, l2.simplify with
  | .lit n1, .lit n2 => some (n1 ≤ n2)
  | _, _ => none

/-- Check if l1 ≤ l2 when both are concrete -/
def leDecide (l1 l2 : Level) : Bool :=
  match leLit? l1 l2 with
  | some b => b
  | none => false  -- Can't decide, assume false

/-- Convert level to subscript string -/
def toSubscript (l : Level) : String :=
  let rec natToSubscript (n : Nat) : String :=
    if n < 10 then
      String.singleton (Char.ofNat (0x2080 + n))  -- ₀₁₂₃₄₅₆₇₈₉
    else
      natToSubscript (n / 10) ++ natToSubscript (n % 10)
  match l with
  | .lit n => natToSubscript n
  | .var v => s!"_{v}"
  | .max l1 l2 => s!"max({toSubscript l1},{toSubscript l2})"
  | .succ l' => s!"({toSubscript l'}+1)"

/-- Convert level to string -/
partial def toStringAux : Level → String
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
