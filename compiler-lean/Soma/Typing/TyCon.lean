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
  deriving Repr

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
  if h : t1.module == t2.module && t1.unique == t2.unique then
    isTrue (by sorry)
  else
    isFalse (by sorry)

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
  deriving Repr

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
    if h : p1 == p2 then isTrue (by sorry) else isFalse (by sorry)
  | .user id1, .user id2 =>
    if h : id1 == id2 then isTrue (by sorry) else isFalse (by sorry)
  | _, _ => isFalse (by sorry)

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

end Soma.Typing
