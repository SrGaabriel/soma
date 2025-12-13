/-
  Constraint Graph for Type Inference

  Key improvements over the old Haskell design:
  1. Explicit constraint graph structure instead of flat lists
  2. Efficient lookup by type variable for dependency tracking
  3. Support for constraint priorities (equality > class constraints)
  4. Tracking of constraint origins for better error messages
-/

import Std.Data.HashMap
import Std.Data.HashSet
import Soma.Infer.Error
import Soma.Infer.Substitution

namespace Soma.Infer

open Std
open Soma.Typing
open Soma.Syntax

/-- A type equality constraint: t1 = t2 -/
structure EqualityConstraint where
  /-- Left-hand side type -/
  lhs : MonoTy
  /-- Right-hand side type -/
  rhs : MonoTy
  /-- Why this constraint exists -/
  purpose : UnifyPurpose
  /-- Span of the expected/lhs type -/
  lhsSpan : Span
  /-- Span of the actual/rhs type -/
  rhsSpan : Span
  /-- Unique identifier for this constraint -/
  id : Nat
  deriving Inhabited

namespace EqualityConstraint

/-- Get all free type variables in this constraint -/
def freeVars (c : EqualityConstraint) : HashSet Nat :=
  let lhsVars := c.lhs.freeVars.foldl (init := ({} : HashSet Nat)) fun acc v => acc.insert v.id
  c.rhs.freeVars.foldl (init := lhsVars) fun acc v => acc.insert v.id

/-- Apply a substitution to this constraint -/
def applySubst (c : EqualityConstraint) (σ : Subst) : EqualityConstraint :=
  { c with lhs := σ.apply c.lhs, rhs := σ.apply c.rhs }

/-- Check if this constraint is trivially satisfied (both sides equal) -/
def isTrivial (c : EqualityConstraint) : Bool :=
  c.lhs == c.rhs

end EqualityConstraint

/-- A type class constraint with origin tracking -/
structure ClassConstraint where
  /-- The class name -/
  className : TyCon
  /-- The type arguments to the class -/
  args : Array MonoTy
  /-- Where this constraint originated -/
  span : Span
  /-- Unique identifier -/
  id : Nat

namespace ClassConstraint

/-- Convert to a Constraint (the simpler representation) -/
def toConstraint (c : ClassConstraint) : Constraint :=
  { className := c.className, args := c.args }

/-- Get all free type variables -/
def freeVars (c : ClassConstraint) : HashSet Nat :=
  c.args.foldl (init := ({} : HashSet Nat)) fun acc ty =>
    ty.freeVars.foldl (init := acc) fun acc v => acc.insert v.id

/-- Apply a substitution -/
def applySubst (c : ClassConstraint) (σ : Subst) : ClassConstraint :=
  { c with args := c.args.map (σ.apply ·) }

/-- Check if this constraint mentions a specific type variable -/
def mentionsVar (c : ClassConstraint) (varId : Nat) : Bool :=
  c.freeVars.contains varId

end ClassConstraint

/-- Priority for constraint solving order -/
inductive ConstraintPriority where
  /-- Simple variable binding (t = T where t is a variable) -/
  | varBinding
  /-- Equality between concrete types -/
  | equality
  /-- Class constraint -/
  | classConstraint
  deriving Repr, BEq

instance : Ord ConstraintPriority where
  compare a b := match a, b with
    | .varBinding, .varBinding => .eq
    | .varBinding, _ => .lt
    | .equality, .varBinding => .gt
    | .equality, .equality => .eq
    | .equality, .classConstraint => .lt
    | .classConstraint, .classConstraint => .eq
    | .classConstraint, _ => .gt

instance : LT ConstraintPriority where
  lt a b := Ord.compare a b = .lt

instance (a b : ConstraintPriority) : Decidable (a < b) :=
  inferInstanceAs (Decidable (Ord.compare a b = .lt))

/-- A constraint graph manages all constraints and their dependencies -/
structure ConstraintGraph where
  /-- All equality constraints -/
  equalities : Array EqualityConstraint
  /-- All class constraints -/
  classes : Array ClassConstraint
  /-- Index: variable ID → equality constraint IDs mentioning it -/
  varToEqualities : HashMap Nat (Array Nat)
  /-- Index: variable ID → class constraint IDs mentioning it -/
  varToClasses : HashMap Nat (Array Nat)
  /-- Next constraint ID -/
  nextId : Nat
  deriving Inhabited

namespace ConstraintGraph

/-- Create an empty constraint graph -/
def empty : ConstraintGraph :=
  { equalities := #[]
  , classes := #[]
  , varToEqualities := {}
  , varToClasses := {}
  , nextId := 0
  }

/-- Add an equality constraint -/
def addEquality (g : ConstraintGraph)
    (lhs rhs : MonoTy) (purpose : UnifyPurpose) (lhsSpan rhsSpan : Span)
    : ConstraintGraph :=
  let c : EqualityConstraint := {
    lhs, rhs, purpose, lhsSpan, rhsSpan, id := g.nextId
  }
  -- Update variable index
  let vars := c.freeVars
  let varToEq := vars.fold (init := g.varToEqualities) fun acc varId =>
    let existing := acc.getD varId #[]
    acc.insert varId (existing.push c.id)
  { g with
    equalities := g.equalities.push c
    varToEqualities := varToEq
    nextId := g.nextId + 1
  }

/-- Add a class constraint -/
def addClass (g : ConstraintGraph)
    (className : TyCon) (args : Array MonoTy) (span : Span)
    : ConstraintGraph :=
  let c : ClassConstraint := {
    className, args, span, id := g.nextId
  }
  -- Update variable index
  let vars := c.freeVars
  let varToCls := vars.fold (init := g.varToClasses) fun acc varId =>
    let existing := acc.getD varId #[]
    acc.insert varId (existing.push c.id)
  { g with
    classes := g.classes.push c
    varToClasses := varToCls
    nextId := g.nextId + 1
  }

/-- Add a Constraint (the simpler representation) -/
def addConstraint (g : ConstraintGraph) (c : Constraint) (span : Span) : ConstraintGraph :=
  g.addClass c.className c.args span

/-- Get all equality constraints mentioning a variable -/
def getEqualitiesForVar (g : ConstraintGraph) (varId : Nat) : Array EqualityConstraint :=
  let ids := g.varToEqualities.getD varId #[]
  ids.filterMap fun id => g.equalities.find? (·.id == id)

/-- Get all class constraints mentioning a variable -/
def getClassesForVar (g : ConstraintGraph) (varId : Nat) : Array ClassConstraint :=
  let ids := g.varToClasses.getD varId #[]
  ids.filterMap fun id => g.classes.find? (·.id == id)

/-- Apply a substitution to all constraints -/
def applySubst (g : ConstraintGraph) (σ : Subst) : ConstraintGraph :=
  let equalities := g.equalities.map (·.applySubst σ)
  let classes := g.classes.map (·.applySubst σ)
  -- Rebuild indices
  let varToEq := equalities.foldl (init := ({} : HashMap Nat (Array Nat))) fun acc c =>
    c.freeVars.fold (init := acc) fun acc varId =>
      let existing := acc.getD varId #[]
      acc.insert varId (existing.push c.id)
  let varToCls := classes.foldl (init := ({} : HashMap Nat (Array Nat))) fun acc c =>
    c.freeVars.fold (init := acc) fun acc varId =>
      let existing := acc.getD varId #[]
      acc.insert varId (existing.push c.id)
  { g with
    equalities
    classes
    varToEqualities := varToEq
    varToClasses := varToCls
  }

/-- Remove trivially satisfied equality constraints -/
def removeTrivial (g : ConstraintGraph) : ConstraintGraph :=
  let equalities := g.equalities.filter (! ·.isTrivial)
  -- Rebuild index
  let varToEq := equalities.foldl (init := ({} : HashMap Nat (Array Nat))) fun acc c =>
    c.freeVars.fold (init := acc) fun acc varId =>
      let existing := acc.getD varId #[]
      acc.insert varId (existing.push c.id)
  { g with equalities, varToEqualities := varToEq }

/-- Get constraints sorted by priority (var bindings first) -/
def sortedEqualities (g : ConstraintGraph) : Array EqualityConstraint :=
  let withPriority := g.equalities.map fun c =>
    let priority := match c.lhs, c.rhs with
      | .var _, _ => ConstraintPriority.varBinding
      | _, .var _ => ConstraintPriority.varBinding
      | _, _ => ConstraintPriority.equality
    (priority, c)
  let sorted := withPriority.qsort fun (p1, _) (p2, _) => p1 < p2
  sorted.map (·.2)

/-- Check if there are any unsolved constraints -/
def hasUnsolved (g : ConstraintGraph) : Bool :=
  g.equalities.any (! ·.isTrivial) || !g.classes.isEmpty

/-- Get all unsolved class constraints -/
def unsolvedClasses (g : ConstraintGraph) : Array ClassConstraint :=
  g.classes

/-- Total number of constraints -/
def size (g : ConstraintGraph) : Nat :=
  g.equalities.size + g.classes.size

/-- Pretty print for debugging -/
def toString (g : ConstraintGraph) : String :=
  let eqStrs := g.equalities.map fun c =>
    s!"  {c.lhs} = {c.rhs} ({c.purpose.describe})"
  let clsStrs := g.classes.map fun c =>
    s!"  {c.className.name} {(c.args.map Ty.toString).toList |> String.intercalate " "}"
  s!"ConstraintGraph:\n  Equalities:\n{"\n".intercalate eqStrs.toList}\n  Classes:\n{"\n".intercalate clsStrs.toList}"

instance : ToString ConstraintGraph := ⟨ConstraintGraph.toString⟩

end ConstraintGraph

/-- Builder for incrementally constructing constraint graphs -/
structure ConstraintBuilder where
  graph : ConstraintGraph
  deriving Inhabited

namespace ConstraintBuilder

def empty : ConstraintBuilder := ⟨ConstraintGraph.empty⟩

def addEquality (b : ConstraintBuilder)
    (lhs rhs : MonoTy) (purpose : UnifyPurpose) (lhsSpan rhsSpan : Span)
    : ConstraintBuilder :=
  ⟨b.graph.addEquality lhs rhs purpose lhsSpan rhsSpan⟩

def addClass (b : ConstraintBuilder)
    (className : TyCon) (args : Array MonoTy) (span : Span)
    : ConstraintBuilder :=
  ⟨b.graph.addClass className args span⟩

def addConstraint (b : ConstraintBuilder) (c : Constraint) (span : Span) : ConstraintBuilder :=
  ⟨b.graph.addConstraint c span⟩

def build (b : ConstraintBuilder) : ConstraintGraph := b.graph

end ConstraintBuilder

end Soma.Infer
