import Soma.Metal.Name
import Soma.Metal.Literal
import Soma.Metal.Scope
import Soma.Syntax.Source

namespace Soma.Metal

open Soma.Typing
open Soma.Syntax (Span)

/-- Patterns parameterized by type info (Unit for untyped, MonoTy for typed) -/
inductive Pattern (α : Type) where
  | var (binding : BindingId) (original : String) (info : α) (span : Span)
  | wildcard (info : α) (span : Span)
  | lit (lit : Literal) (span : Span)
  | ctor (name : Name) (args : Array (Pattern α)) (info : α) (span : Span)
  | tuple (elements : Array (Pattern α)) (info : α) (span : Span)
  | array (elements : Array (Pattern α)) (info : α) (span : Span)
  | cons (head : Pattern α) (tail : Pattern α) (info : α) (span : Span)
  | as (binding : BindingId) (original : String) (inner : Pattern α) (info : α) (span : Span)
  deriving Inhabited

/-- Untyped patterns (before type checking) -/
abbrev UntypedPattern := Pattern Unit

/-- Typed patterns (after type checking) -/
abbrev TypedPattern := Pattern MonoTy

namespace Pattern

/-- Get the span of a pattern -/
def span : Pattern α → Span
  | .var _ _ _ s => s
  | .wildcard _ s => s
  | .lit _ s => s
  | .ctor _ _ _ s => s
  | .tuple _ _ s => s
  | .array _ _ s => s
  | .cons _ _ _ s => s
  | .as _ _ _ _ s => s

/-- Get all binding IDs introduced by this pattern -/
partial def bindings : Pattern α → Array BindingId
  | .var b _ _ _ => #[b]
  | .wildcard _ _ => #[]
  | .lit _ _ => #[]
  | .ctor _ args _ _ => args.foldl (fun acc p => acc ++ p.bindings) #[]
  | .tuple elems _ _ => elems.foldl (fun acc p => acc ++ p.bindings) #[]
  | .array elems _ _ => elems.foldl (fun acc p => acc ++ p.bindings) #[]
  | .cons h t _ _ => h.bindings ++ t.bindings
  | .as b _ inner _ _ => #[b] ++ inner.bindings

/-- Get bindings as (id, name) pairs -/
partial def bindingsWithNames : Pattern α → Array (BindingId × String)
  | .var b orig _ _ => #[(b, orig)]
  | .wildcard _ _ => #[]
  | .lit _ _ => #[]
  | .ctor _ args _ _ => args.foldl (fun acc p => acc ++ p.bindingsWithNames) #[]
  | .tuple elems _ _ => elems.foldl (fun acc p => acc ++ p.bindingsWithNames) #[]
  | .array elems _ _ => elems.foldl (fun acc p => acc ++ p.bindingsWithNames) #[]
  | .cons h t _ _ => h.bindingsWithNames ++ t.bindingsWithNames
  | .as b orig inner _ _ => #[(b, orig)] ++ inner.bindingsWithNames

/-- Extend a scope with the bindings from this pattern -/
def extendScope (p : Pattern α) (s : Scope) : Scope :=
  let bs : List BindingId := p.bindings.toList
  bs ++ s

/-- Extend a scope with multiple patterns -/
def extendScopeMany (ps : Array (Pattern α)) (s : Scope) : Scope :=
  ps.foldl (fun acc p => p.extendScope acc) s

/-- Map over the type info in a pattern -/
partial def map (f : α → β) : Pattern α → Pattern β
  | .var b orig info s => .var b orig (f info) s
  | .wildcard info s => .wildcard (f info) s
  | .lit l s => .lit l s
  | .ctor name args info s => .ctor name (args.map (map f)) (f info) s
  | .tuple elems info s => .tuple (elems.map (map f)) (f info) s
  | .array elems info s => .array (elems.map (map f)) (f info) s
  | .cons h t info s => .cons (map f h) (map f t) (f info) s
  | .as b orig inner info s => .as b orig (map f inner) (f info) s

end Pattern

end Soma.Metal
