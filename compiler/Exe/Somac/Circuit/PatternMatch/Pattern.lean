import Soma.Core.Expr
import Soma.Core.Literal

namespace Somac.Circuit.PatternMatch

open Soma.Core (Pattern)
open Soma (Unique)
open Soma.Core (Literal)

/-- A simplified pattern for decision tree compilation.

    This representation strips type information and normalizes
    all constructor-like patterns to a uniform `ctor` form.
-/
inductive SimplePattern where
  /-- Matches anything, binds nothing -/
  | wildcard
  /-- Matches anything, binds the value to a variable -/
  | var (binding : Unique) (name : String)
  /-- Matches a constructor with given tag, expecting `arity` fields -/
  | ctor (tag : Nat) (arity : Nat) (args : Array SimplePattern)
  /-- Matches a literal value exactly -/
  | lit (value : Literal)
  /-- Matches inner pattern and also binds the whole value -/
  | as (binding : Unique) (name : String) (inner : SimplePattern)
  deriving Repr, Inhabited, BEq

namespace SimplePattern

/-- Check if pattern is a wildcard or variable (matches any value) -/
def isWildcardOrVar : SimplePattern → Bool
  | .wildcard => true
  | .var _ _ => true
  | .as _ _ inner => inner.isWildcardOrVar
  | _ => false

/-- Check if pattern constrains the value (is not a wildcard/var) -/
def isConstraining : SimplePattern → Bool
  | .wildcard => false
  | .var _ _ => false
  | .as _ _ inner => inner.isConstraining
  | .ctor _ _ _ => true
  | .lit _ => true

/-- Get the constructor tag if this is a constructor pattern -/
def getCtorTag? : SimplePattern → Option Nat
  | .ctor tag _ _ => some tag
  | .as _ _ inner => inner.getCtorTag?
  | _ => none

/-- Get the constructor arity if this is a constructor pattern -/
def getCtorArity? : SimplePattern → Option Nat
  | .ctor _ arity _ => some arity
  | .as _ _ inner => inner.getCtorArity?
  | _ => none

/-- Get constructor arguments if this is a constructor pattern -/
def getCtorArgs? : SimplePattern → Option (Array SimplePattern)
  | .ctor _ _ args => some args
  | .as _ _ inner => inner.getCtorArgs?
  | _ => none

/-- Get the literal value if this is a literal pattern -/
def getLit? : SimplePattern → Option Literal
  | .lit v => some v
  | .as _ _ inner => inner.getLit?
  | _ => none

/-- Get the inner pattern, stripping as-patterns -/
def stripAs : SimplePattern → SimplePattern
  | .as _ _ inner => inner.stripAs
  | p => p

/-- Collect all variable bindings from a pattern (depth-first) -/
partial def collectBindings : SimplePattern → Array (Unique × String)
  | .wildcard => #[]
  | .var b n => #[(b, n)]
  | .ctor _ _ args => args.foldl (fun acc p => acc ++ p.collectBindings) #[]
  | .lit _ => #[]
  | .as b n inner => #[(b, n)] ++ inner.collectBindings

/-- Pretty print a pattern for debugging -/
partial def format : SimplePattern → String
  | .wildcard => "_"
  | .var _ name => name
  | .ctor tag 0 #[] => s!"C{tag}"
  | .ctor tag _ args =>
    let argStrs := args.toList.map format
    s!"C{tag}({", ".intercalate argStrs})"
  | .lit (.int n) => toString n
  | .lit (.float f) => toString f
  | .lit (.bool b) => toString b
  | .lit (.string s) => s!"\"{s}\""
  | .as _ name inner => s!"{name}@{inner.format}"

instance : ToString SimplePattern := ⟨format⟩

end SimplePattern

/-! ## Pattern Simplification -/

/-- Context for pattern simplification -/
structure SimplifyCtx where
  /-- Pre-resolved variant label → tag mapping -/
  variantTags : Std.HashMap String Nat := {}
  deriving Inhabited

/-- Well-known tags for list-like structures -/
def listNilTag : Nat := 0
def listConsTag : Nat := 1

/-- Well-known tag for tuples (single constructor) -/
def tupleTag : Nat := 0

/-- Simplify a Core pattern to a SimplePattern -/
partial def simplifyPattern (ctx : SimplifyCtx) : Pattern → SimplePattern
  | .var (some u) =>
    .var u u.original
  | .var none =>
    .wildcard
  | .lit literal =>
    .lit literal
  | .ctor _name tag args =>
    let simplifiedArgs := args.map (simplifyPattern ctx)
    .ctor tag args.size simplifiedArgs
  | .wildcard =>
    .wildcard
  | .inject label arg =>
    let tag := ctx.variantTags.getD label (label.hash.toNat % 0xFFFF)
    let args := match arg with
      | some p => #[simplifyPattern ctx p]
      | none => #[]
    .ctor tag args.size args

/-- Simplify a list of patterns -/
def simplifyPatterns (ctx : SimplifyCtx) (pats : Array Pattern)
    : Array SimplePattern :=
  pats.map (simplifyPattern ctx)

/-- Collect all variant label names from a pattern -/
partial def collectVariantLabels : Pattern → Array String
  | .inject label arg =>
    #[label] ++ match arg with
      | some p => collectVariantLabels p
      | none => #[]
  | .ctor _ _ args => args.foldl (fun acc p => acc ++ collectVariantLabels p) #[]
  | _ => #[]

/-- Collect all variant labels from a list of Core arms -/
def collectArmsVariantLabels (arms : Array Soma.Core.Arm) : Array String :=
  let labels := arms.foldl (fun acc arm =>
    arm.patterns.foldl (fun acc2 p => acc2 ++ collectVariantLabels p) acc) #[]
  -- Deduplicate
  labels.foldl (fun acc l => if acc.contains l then acc else acc.push l) #[]

end Somac.Circuit.PatternMatch
