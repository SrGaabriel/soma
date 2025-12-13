/-
  Soma.Unique - Unique identifiers for compiler-generated names

  This module provides a rigid, type-safe unique identifier system matching
  the Haskell compiler's design. Uniques are globally unique within a module
  and carry enough context for debugging and cross-module disambiguation.
-/

namespace Soma

/-- A unique identifier within the compiler.

    Uniques are the foundation of the name system. They provide:
    - Global uniqueness within a module (via `id`)
    - Cross-module disambiguation (via `module`)
    - Debugging/error message support (via `original`)

    Two Uniques are equal iff they have the same `id` AND `module`.
    The `original` name is purely for display purposes.
-/
structure Unique where
  /-- Numeric ID, unique within the module -/
  id : Nat
  /-- Module where this unique was created -/
  module : String
  /-- Original source name (for debugging/error messages) -/
  original : String
  deriving Repr

namespace Unique

/-- Equality is based on (id, module) only - original name is for display -/
instance : BEq Unique where
  beq u1 u2 := u1.id == u2.id && u1.module == u2.module

/-- Ordering for use in sorted collections -/
instance : Ord Unique where
  compare u1 u2 :=
    match compare u1.module u2.module with
    | .eq => compare u1.id u2.id
    | other => other

instance : Hashable Unique where
  hash u := mixHash (hash u.id) (hash u.module)

/-- DecidableEq based on structural equality -/
instance : DecidableEq Unique := fun u1 u2 =>
  match decEq u1.id u2.id, decEq u1.module u2.module, decEq u1.original u2.original with
  | isTrue h1, isTrue h2, isTrue h3 =>
    isTrue (by cases u1; cases u2; simp_all)
  | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
  | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
  | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)

/-- Display name for error messages -/
def display (u : Unique) : String := u.original

/-- Fully qualified display name -/
def qualifiedDisplay (u : Unique) : String :=
  if u.module.isEmpty then u.original
  else s!"{u.module}.{u.original}"

/-- Mangled name for code generation (guaranteed unique) -/
def mangle (u : Unique) : String :=
  let sanitized := u.original.map fun c =>
    if c.isAlphanum || c == '_' then c else '_'
  let modSanitized := u.module.map fun c =>
    if c.isAlphanum || c == '_' then c else '_'
  s!"{modSanitized}_{sanitized}_{u.id}"

instance : ToString Unique := ⟨Unique.display⟩

end Unique

/-- State for generating unique identifiers -/
structure UniqueSupply where
  /-- Next ID to assign -/
  nextId : Nat
  /-- Module name for all generated uniques -/
  module : String
  deriving Repr

namespace UniqueSupply

/-- Create a fresh supply for a module -/
def initial (moduleName : String) : UniqueSupply :=
  { nextId := 0, module := moduleName }

/-- Generate a fresh unique -/
def fresh (supply : UniqueSupply) (original : String) : Unique × UniqueSupply :=
  let u : Unique := { id := supply.nextId, module := supply.module, original }
  (u, { supply with nextId := supply.nextId + 1 })

/-- Generate a derived unique from an existing one (for synthetic names) -/
def freshFrom (supply : UniqueSupply) (base : Unique) (suffix : String) : Unique × UniqueSupply :=
  let newOriginal := s!"{base.original}${suffix}"
  let u : Unique := { id := supply.nextId, module := base.module, original := newOriginal }
  (u, { supply with nextId := supply.nextId + 1 })

end UniqueSupply

/-- Monad transformer for unique generation -/
abbrev UniqueT (m : Type → Type) := StateT UniqueSupply m

/-- Simple unique monad -/
abbrev UniqueM := StateM UniqueSupply

namespace UniqueM

/-- Generate a fresh unique -/
def fresh (original : String) : UniqueM Unique := do
  let supply ← get
  let (u, supply') := supply.fresh original
  set supply'
  pure u

/-- Generate a derived unique -/
def freshFrom (base : Unique) (suffix : String) : UniqueM Unique := do
  let supply ← get
  let (u, supply') := supply.freshFrom base suffix
  set supply'
  pure u

/-- Run the unique monad -/
def run (m : UniqueM α) (moduleName : String) : α × UniqueSupply :=
  StateT.run m (UniqueSupply.initial moduleName)

/-- Run and discard the supply -/
def run' (m : UniqueM α) (moduleName : String) : α :=
  (run m moduleName).1

theorem fresh_ids_distinct (supply : UniqueSupply) (orig1 orig2 : String) :
    let (u1, supply') := supply.fresh orig1
    let (u2, _) := supply'.fresh orig2
    u1.id ≠ u2.id := by
  intro h
  simp only at h
  omega

end UniqueM

end Soma
