import Soma.Typing.Kind
import Soma.Typing.Primitive

namespace Soma.Typing

/-- Unique identifier for a user-defined type -/
structure TypeId where
  module : String
  name : String
  unique : Nat
  deriving Repr, BEq, Hashable, Ord, DecidableEq

namespace TypeId

def toString (id : TypeId) : String :=
  if id.module.isEmpty then id.name
  else s!"{id.module}.{id.name}"

instance : ToString TypeId := ⟨TypeId.toString⟩

end TypeId

/-- Type constructor identity -/
inductive TyCon where
  /-- A primitive/built-in type -/
  | prim (p : Primitive)
  /-- A user-defined type -/
  | user (id : TypeId)
  deriving Repr, BEq, Hashable, DecidableEq

namespace TyCon

/-- Get the name of a type constructor -/
def name : TyCon → String
  | .prim p => p.name
  | .user id => id.name

instance : ToString TyCon := ⟨TyCon.name⟩

/-- Get the kind of a type constructor -/
def kind : TyCon → Kind
  | .prim p => p.kind
  | .user _ => .star -- TODO: Review vomit-inducing workaround, currently user types default to *

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

end TyCon

end Soma.Typing
