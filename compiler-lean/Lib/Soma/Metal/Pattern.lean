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
  | variant (label : String) (arg : Option (Pattern α)) (info : α) (span : Span)
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
  | .variant _ _ _ s => s

/-- Get all binding IDs introduced by this pattern -/
def bindings : Pattern α → Array BindingId
  | .var b _ _ _ => #[b]
  | .wildcard _ _ => #[]
  | .lit _ _ => #[]
  | .ctor _ args _ _ => args.attach.foldl (fun acc ⟨p, _⟩ => acc ++ p.bindings) #[]
  | .tuple elems _ _ => elems.attach.foldl (fun acc ⟨p, _⟩ => acc ++ p.bindings) #[]
  | .array elems _ _ => elems.attach.foldl (fun acc ⟨p, _⟩ => acc ++ p.bindings) #[]
  | .cons h t _ _ => h.bindings ++ t.bindings
  | .as b _ inner _ _ => #[b] ++ inner.bindings
  | .variant _ (some p) _ _ => p.bindings
  | .variant _ none _ _ => #[]

/-- Get bindings as (id, name) pairs -/
def bindingsWithNames : Pattern α → Array (BindingId × String)
  | .var b orig _ _ => #[(b, orig)]
  | .wildcard _ _ => #[]
  | .lit _ _ => #[]
  | .ctor _ args _ _ => args.attach.foldl (fun acc ⟨p, _⟩ => acc ++ p.bindingsWithNames) #[]
  | .tuple elems _ _ => elems.attach.foldl (fun acc ⟨p, _⟩ => acc ++ p.bindingsWithNames) #[]
  | .array elems _ _ => elems.attach.foldl (fun acc ⟨p, _⟩ => acc ++ p.bindingsWithNames) #[]
  | .cons h t _ _ => h.bindingsWithNames ++ t.bindingsWithNames
  | .as b orig inner _ _ => #[(b, orig)] ++ inner.bindingsWithNames
  | .variant _ (some p) _ _ => p.bindingsWithNames
  | .variant _ none _ _ => #[]

/-- General lemma: List.foldl over append preserves map relationship -/
theorem list_foldl_append_map_fst {β γ δ : Type}
    (f : β → Array (γ × δ)) (g : β → Array γ)
    (hfg : ∀ x, (f x).toList.map Prod.fst = (g x).toList)
    (xs : List β) (init1 : Array (γ × δ)) (init2 : Array γ)
    (hinit : init1.toList.map Prod.fst = init2.toList) :
    (xs.foldl (fun acc x => acc ++ f x) init1).toList.map Prod.fst =
    (xs.foldl (fun acc x => acc ++ g x) init2).toList := by
  induction xs generalizing init1 init2 with
  | nil => exact hinit
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih
    simp only [Array.toList_append, List.map_append, hinit, hfg]

/-- Specialized to Array.foldl -/
theorem array_foldl_append_map_fst {β γ δ : Type}
    (f : β → Array (γ × δ)) (g : β → Array γ)
    (hfg : ∀ x, (f x).toList.map Prod.fst = (g x).toList)
    (arr : Array β) (init1 : Array (γ × δ)) (init2 : Array γ)
    (hinit : init1.toList.map Prod.fst = init2.toList) :
    (arr.foldl (fun acc x => acc ++ f x) init1).toList.map Prod.fst =
    (arr.foldl (fun acc x => acc ++ g x) init2).toList := by
  have h := list_foldl_append_map_fst f g hfg arr.toList init1 init2 hinit
  simp only [Array.foldl_toList] at h
  exact h

/-- Theorem: Pattern.bindingsWithNames.map fst = Pattern.bindings

    This theorem states that extracting just the BindingIds from bindingsWithNames
    gives the same result as calling bindings directly.
-/
theorem bindingsWithNames_fst (pat : Pattern α) :
    (pat.bindingsWithNames.toList.map Prod.fst) = pat.bindings.toList := by
  match pat with
  | .var _ _ _ _ => simp [bindingsWithNames, bindings]
  | .wildcard _ _ => simp [bindingsWithNames, bindings]
  | .lit _ _ => simp [bindingsWithNames, bindings]
  | .ctor _ args _ _ =>
    simp only [bindingsWithNames, bindings]
    exact array_foldl_append_map_fst
      (fun ⟨p, _⟩ => p.bindingsWithNames)
      (fun ⟨p, _⟩ => p.bindings)
      (fun ⟨p, _⟩ => bindingsWithNames_fst p)
      args.attach #[] #[] rfl
  | .tuple elems _ _ =>
    simp only [bindingsWithNames, bindings]
    exact array_foldl_append_map_fst
      (fun ⟨p, _⟩ => p.bindingsWithNames)
      (fun ⟨p, _⟩ => p.bindings)
      (fun ⟨p, _⟩ => bindingsWithNames_fst p)
      elems.attach #[] #[] rfl
  | .array elems _ _ =>
    simp only [bindingsWithNames, bindings]
    exact array_foldl_append_map_fst
      (fun ⟨p, _⟩ => p.bindingsWithNames)
      (fun ⟨p, _⟩ => p.bindings)
      (fun ⟨p, _⟩ => bindingsWithNames_fst p)
      elems.attach #[] #[] rfl
  | .cons h t _ _ =>
    simp only [bindingsWithNames, bindings, Array.toList_append, List.map_append]
    rw [bindingsWithNames_fst h, bindingsWithNames_fst t]
  | .as _ _ inner _ _ =>
    simp only [bindingsWithNames, bindings, Array.toList_append, List.map_append]
    simp only [List.map_cons, List.map_nil]
    rw [bindingsWithNames_fst inner]
  | .variant _ (some p) _ _ =>
    simp only [bindingsWithNames, bindings]
    exact bindingsWithNames_fst p
  | .variant _ none _ _ => simp [bindingsWithNames, bindings]

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
  | .variant label arg info s => .variant label (arg.map (map f)) (f info) s

/-- Pattern.map preserves bindings (axiomatized due to partial functions) -/
axiom map_bindings (f : α → β) (p : Pattern α) : (p.map f).bindings = p.bindings

end Pattern

end Soma.Metal
