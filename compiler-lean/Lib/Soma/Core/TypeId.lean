import Soma.Unique
import Lean.Data.Json

namespace Soma.Core

open Soma

/-- Unique identifier for a user-defined type -/
structure TypeId where
  /-- Module where this type is defined -/
  module : String
  /-- Display name of the type -/
  name : String
  /-- Unique numeric identifier within the module -/
  unique : Nat
  deriving Repr, Inhabited

instance : Lean.ToJson TypeId where
  toJson id := .mkObj [
    ("module", .str id.module),
    ("name", .str id.name),
    ("unique", .num id.unique)
  ]

instance : Lean.FromJson TypeId where
  fromJson? j := do
    let module ← j.getObjValAs? String "module"
    let name ← j.getObjValAs? String "name"
    let unique ← j.getObjValAs? Nat "unique"
    pure ⟨module, name, unique⟩

namespace TypeId

/-- Equality based on (module, unique) only -/
instance : BEq TypeId where
  beq t1 t2 := t1.module == t2.module && t1.unique == t2.unique

/-- Hash based on (module, unique) only -/
instance : Hashable TypeId where
  hash t := mixHash (hash t.module) (hash t.unique)

/-- Ordering based on (module, unique) -/
instance : Ord TypeId where
  compare t1 t2 :=
    match compare t1.module t2.module with
    | .eq => compare t1.unique t2.unique
    | other => other

instance : DecidableEq TypeId := fun t1 t2 =>
  match decEq t1.module t2.module, decEq t1.name t2.name, decEq t1.unique t2.unique with
  | isTrue h1, isTrue h2, isTrue h3 =>
    isTrue (by cases t1; cases t2; simp_all)
  | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
  | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
  | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)

/-- Display the type name (qualified if module is non-empty) -/
def toString (id : TypeId) : String :=
  if id.module.isEmpty then id.name
  else s!"{id.module}.{id.name}"

instance : ToString TypeId := ⟨TypeId.toString⟩

/-- Create a TypeId from a Unique -/
def fromUnique (u : Unique) : TypeId :=
  { module := u.module, name := u.original, unique := u.id }

/-- Create a simple TypeId with just a name (for built-in types or testing) -/
def simple (name : String) (unique : Nat := 0) : TypeId :=
  { module := "", name := name, unique := unique }

/-- Reserved module name for built-in primitives -/
def builtinModule : String := "$builtin"

/-- Create a TypeId for a built-in primitive type -/
def builtin (name : String) (unique : Nat) : TypeId :=
  { module := builtinModule, name := name, unique := unique }

end TypeId

end Soma.Core
