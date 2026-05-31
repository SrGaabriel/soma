import Soma.Core.Value
import Soma.Core.Level
import Soma.Core.Eval
import Soma.Dependent.Monad
import Soma.Dependent.Error
import Soma.Dependent.Prelude

namespace Soma.Dependent.Totality

open Soma.Core
open Soma.Syntax (Span)
open Soma (Unique)

/-- A placeholder QualifiedName for use in Inhabited instances -/
def dummyName : QualifiedName := ⟨{ id := 0, module := "$totality", original := "$dummy" }⟩

/-- The totality status of a definition -/
inductive TotalityStatus where
  | isPartial -- Function is partial (default)
  | isTotal -- Function is total (verified to terminate)
  | isUnknown -- Function totality is unknown (needs checking)
  deriving Repr, BEq, Inhabited

/-- Information about a function for totality checking -/
structure FunctionInfo where
  name : QualifiedName
  markedTotal : Bool
  status : TotalityStatus
  params : Array String
  paramIds : Array Unique
  fnType : Value
  span : Span

instance : Inhabited FunctionInfo where
  default := {
    name := dummyName
    markedTotal := false
    status := .isPartial
    params := #[]
    paramIds := #[]
    fnType := Value.vType .zero
    span := Span.uninhabited
  }

/-- A single structural projection step into a value -/
inductive Proj where
  | con (ctor : String) (idx : Nat)
  | variant (label : String) (idx : Nat)
  | field (name : String)
  | tuple (idx : Nat)
  deriving Repr, BEq, Hashable, Inhabited

/-- A sequence of projections from a parameter -/
abbrev AccessPath := List Proj

/-- Is `p` a (not necessarily strict) prefix of `q`? -/
def AccessPath.isPrefixOf : AccessPath → AccessPath → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a == b && AccessPath.isPrefixOf as bs

/-- A structural position -/
structure Prov where
  root : Nat
  path : AccessPath
  deriving Repr, BEq, Hashable, Inhabited

namespace Prov

/-- Extend a position by one projection -/
def extend (p : Prov) (proj : Proj) : Prov := { p with path := p.path ++ [proj] }

/-- Extend a position by several projections -/
def extendAll (p : Prov) (projs : AccessPath) : Prov := { p with path := p.path ++ projs }

instance : ToString Prov where
  toString p := Id.run do
    let mut s := s!"p{p.root}"
    for proj in p.path do
      s := s ++ (match proj with
        | .con c i => s!".{c}[{i}]"
        | .variant l i => s!".{l}<{i}>"
        | .field n => s!".{n}"
        | .tuple i => s!".{i}")
    return s

end Prov

/-- The relation between two structural positions on a recursive call -/
inductive SizeRel where
  | lt
  | le
  deriving Repr, BEq, Inhabited

namespace SizeRel

/-- `lt` dominates `le` when several witnesses are available for the same pair -/
def join : SizeRel → SizeRel → SizeRel
  | .lt, _ => .lt
  | _, .lt => .lt
  | .le, .le => .le

/-- Sequential composition along a call path -/
def compose : SizeRel → SizeRel → SizeRel
  | .lt, _ => .lt
  | _, .lt => .lt
  | .le, .le => .le

end SizeRel

/-- Registry of function totality status -/
structure TotalityRegistry where
  functions : Std.HashMap String TotalityStatus := {}
  deriving Inhabited

namespace TotalityRegistry

def empty : TotalityRegistry := {}

def register (reg : TotalityRegistry) (name : String) (status : TotalityStatus) : TotalityRegistry :=
  { reg with functions := reg.functions.insert name status }

def lookup (reg : TotalityRegistry) (name : String) : Option TotalityStatus :=
  reg.functions.get? name

end TotalityRegistry

end Soma.Dependent.Totality
