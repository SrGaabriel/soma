import Kenosis

namespace Soma.Core

open Kenosis

/-- De Bruijn level (counts from bottom of context, unlike indices which count from top) -/
structure DeBruijnLvl where
  lvl : Nat
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited, Serialize, Deserialize

namespace DeBruijnLvl

def zero : DeBruijnLvl := ⟨0⟩

def succ (l : DeBruijnLvl) : DeBruijnLvl := ⟨l.lvl + 1⟩

def toNat (l : DeBruijnLvl) : Nat := l.lvl

instance : ToString DeBruijnLvl where
  toString l := s!"@{l.lvl}"

end DeBruijnLvl

/-- Metavariable identifier -/
structure MetaId where
  id : Nat
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited, Serialize, Deserialize

namespace MetaId

instance : ToString MetaId where
  toString m := s!"?{m.id}"

end MetaId

/-- A bound variable in a value -/
structure BoundVar where
  name : String
  level : DeBruijnLvl
  deriving Repr, BEq, Hashable, Inhabited, Serialize, Deserialize

namespace BoundVar

instance : ToString BoundVar where
  toString v := s!"{v.name}@{v.level.lvl}"

end BoundVar

end Soma.Core
