import Soma.Syntax.Source
import Soma.Core.Value
import Kenosis

namespace Soma.Project

open Soma
open Soma.Syntax
open Soma.Core
open Kenosis

/-- The kind of a symbol, determining its namespace and semantics -/
inductive SymbolKind where
  /-- Top-level function/value binding (type stored separately in SymbolEnv) -/
  | binding
  /-- Data constructor with parent type name and tag -/
  | dataCon (parentType : String) (tag : Nat)
  /-- Type name (data, struct, type alias) -/
  | type
  /-- Type class name -/
  | typeClass
  /-- Method declared in a type class -/
  | typeClassMethod (className : String)
  /-- Method implementation in an instance -/
  | instanceMethod (instanceDesc : String) (className : String)
  /-- Local let binding -/
  | letBinding
  /-- Lambda parameter -/
  | lambdaParam
  /-- Pattern variable -/
  | patternVar
  /-- As-pattern binding (x@pat) -/
  | patternAs
  /-- Compose block binding -/
  | composeBinding
  /-- Compiler intrinsic binding -/
  | intrinsicBinding
  /-- Compiler intrinsic type -/
  | intrinsicType
  deriving Repr, BEq, Serialize, Deserialize

namespace SymbolKind

/-- Check if this is a value-level symbol (vs type-level) -/
def isValue : SymbolKind → Bool
  | .binding | .dataCon _ _ | .letBinding | .lambdaParam
  | .patternVar | .patternAs | .composeBinding
  | .typeClassMethod _ | .instanceMethod _ _
  | .intrinsicBinding => true
  | .type | .typeClass | .intrinsicType => false

/-- Check if this is a type-level symbol -/
def isType : SymbolKind → Bool
  | .type | .typeClass | .intrinsicType => true
  | _ => false

/-- Check if this is an intrinsic -/
def isIntrinsic : SymbolKind → Bool
  | .intrinsicBinding | .intrinsicType => true
  | _ => false

end SymbolKind

/-- A fully resolved symbol with complete provenance -/
structure Symbol where
  /-- Unique ID -/
  unique : Unique
  /-- The source name -/
  name : String
  /-- What kind of symbol this is -/
  kind : SymbolKind
  /-- Module where this symbol is defined -/
  module : String
  /-- Package containing the module -/
  package : String
  /-- Source location where defined -/
  span : Span
  deriving Repr, Serialize, Deserialize

namespace Symbol

instance : BEq Symbol where
  beq s1 s2 := s1.unique == s2.unique

instance : Ord Symbol where
  compare s1 s2 :=
    compare s1.unique s2.unique

instance : Hashable Symbol where
  hash s :=
    hash s.unique

/-- Display name for error messages -/
def display (s : Symbol) : String := s.name

/-- Fully qualified display name -/
def qualifiedDisplay (s : Symbol) : String :=
  if s.module.isEmpty then s.name
  else s!"{s.module}.{s.name}"

instance : ToString Symbol := ⟨Symbol.display⟩

/-- Check if this is a value-level symbol -/
def isValue (s : Symbol) : Bool := s.kind.isValue

/-- Check if this is a type-level symbol -/
def isType (s : Symbol) : Bool := s.kind.isType

/-- Check if this is an intrinsic -/
def isIntrinsic (s : Symbol) : Bool := s.kind.isIntrinsic

/-- Check if this is a data constructor -/
def isDataCon (s : Symbol) : Bool :=
  match s.kind with
  | .dataCon _ _ => true
  | _ => false

/-- Check if this is an instance method -/
def isInstanceMethod (s : Symbol) : Bool :=
  match s.kind with
  | .instanceMethod _ _ => true
  | _ => false

end Symbol

/-- A symbol environment maps symbols to their types (as Core.Value) -/
abbrev SymbolEnv := Std.HashMap Symbol Value

/-- Instance metadata for type class instances - maps class name to array of (instance type args, implementing symbol) -/
abbrev InstanceMetadata := Std.HashMap String (Array (Array Value × Symbol))

end Soma.Project
