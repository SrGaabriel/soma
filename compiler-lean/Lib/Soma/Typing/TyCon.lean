import Soma.Typing.Kind
import Soma.Typing.Primitive
import Soma.Unique

namespace Soma.Typing

open Soma

/-- Unique identifier for a user-defined type -/
structure TypeId where
  module : String
  name : String
  unique : Nat
  kind : Kind := .star
  deriving Repr, Inhabited

namespace TypeId

/-- Equality based on (module, unique) only - name is for display -/
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
  match decEq t1.module t2.module, decEq t1.name t2.name, decEq t1.unique t2.unique, decEq t1.kind t2.kind with
  | isTrue h1, isTrue h2, isTrue h3, isTrue h4 =>
    isTrue (by cases t1; cases t2; simp_all)
  | isFalse h, _, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
  | _, isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
  | _, _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
  | _, _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)

/-- Display the type name (qualified if module is non-empty) -/
def toString (id : TypeId) : String :=
  if id.module.isEmpty then id.name
  else s!"{id.module}.{id.name}"

instance : ToString TypeId := ⟨TypeId.toString⟩

/-- Create a TypeId from a Unique -/
def fromUnique (u : Unique) (kind : Kind := .star) : TypeId :=
  { module := u.module, name := u.original, unique := u.id, kind }

end TypeId

/-- Type constructor identity -/
inductive TyCon where
  /-- A primitive/built-in type -/
  | prim (p : Primitive)
  /-- A user-defined type -/
  | user (id : TypeId)
  deriving Repr, Inhabited

namespace TyCon

instance : BEq TyCon where
  beq
    | .prim p1, .prim p2 => p1 == p2
    | .user id1, .user id2 => id1 == id2
    | _, _ => false

instance : Hashable TyCon where
  hash
    | .prim p => mixHash 0 (hash p)
    | .user id => mixHash 1 (hash id)

instance : DecidableEq TyCon := fun c1 c2 =>
  match c1, c2 with
  | .prim p1, .prim p2 =>
    match decEq p1 p2 with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .user id1, .user id2 =>
    match decEq id1 id2 with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .prim _, .user _ => isFalse (by intro h; cases h)
  | .user _, .prim _ => isFalse (by intro h; cases h)

/-- Get the name of a type constructor -/
def name : TyCon → String
  | .prim p => p.name
  | .user id => id.name

instance : ToString TyCon := ⟨TyCon.name⟩

/-- Get the kind of a type constructor -/
def kind : TyCon → Kind
  | .prim p => p.kind
  | .user id => id.kind

/-- Get the module of a type constructor (None for primitives) -/
def module? : TyCon → Option String
  | .prim _ => none
  | .user id => some id.module

/-- Check if this is a primitive type constructor -/
def isPrim : TyCon → Bool
  | .prim _ => true
  | .user _ => false

/-- Check if this is a user-defined type constructor -/
def isUser : TyCon → Bool
  | .prim _ => false
  | .user _ => true

/-- Convenient constructors for common primitives -/
def int : TyCon := .prim .int
def long : TyCon := .prim .long
def short : TyCon := .prim .short
def byte : TyCon := .prim .byte
def float : TyCon := .prim .float
def double : TyCon := .prim .double
def bool : TyCon := .prim .bool
def string : TyCon := .prim .string
def unit : TyCon := .prim .unit
def array : TyCon := .prim .array
def closurePtr : TyCon := .prim .closurePtr
def ptr : TyCon := .prim .ptr
def ref : TyCon := .prim .ref
def io : TyCon := .prim .io

def tuple (n : Nat) : TyCon := .prim (.tuple n)

/-- Create a user-defined type constructor -/
def mkUser (module : String) (name : String) (unique : Nat) (kind : Kind := .star) : TyCon :=
  .user { module, name, unique, kind }

/-- Create a user-defined type constructor from a Unique -/
def fromUnique (u : Unique) (kind : Kind := .star) : TyCon :=
  .user (TypeId.fromUnique u kind)

end TyCon

-- Built-in type class names as TyCons
namespace TypeClassName
  def eq : TyCon := .prim .classEq
  def ord : TyCon := .prim .classOrd
  def show_ : TyCon := .prim .classShow
  def num : TyCon := .prim .classNum
  def functor : TyCon := .prim .classFunctor
  def monad : TyCon := .prim .classMonad
end TypeClassName

end Soma.Typing
