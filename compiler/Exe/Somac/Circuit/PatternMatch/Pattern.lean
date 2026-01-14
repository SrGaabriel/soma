import Soma.Metal.Pattern
import Soma.Metal.Literal
import Soma.Metal.Scope
import Std.Data.HashMap

namespace Somac.Circuit.PatternMatch

open Soma.Metal (Pattern Literal BindingId Name)

/-- A simplified pattern for decision tree compilation.

    This representation strips type information and normalizes
    all constructor-like patterns to a uniform `ctor` form.
-/
inductive SimplePattern where
  /-- Matches anything, binds nothing -/
  | wildcard
  /-- Matches anything, binds the value to a variable -/
  | var (binding : BindingId) (name : String)
  /-- Matches a constructor with given tag, expecting `arity` fields -/
  | ctor (tag : Nat) (arity : Nat) (args : Array SimplePattern)
  /-- Matches a literal value exactly -/
  | lit (value : Literal)
  /-- Matches inner pattern and also binds the whole value -/
  | as (binding : BindingId) (name : String) (inner : SimplePattern)
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
partial def collectBindings : SimplePattern → Array (BindingId × String)
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
  | .lit (.bool b) => toString b
  | .lit (.string s) => s!"\"{s}\""
  | .as _ name inner => s!"{name}@{inner.format}"

instance : ToString SimplePattern := ⟨format⟩

end SimplePattern

/-! ## Constructor Information -/

/-- Information about a single constructor -/
structure ConstructorInfo where
  /-- The data type this constructor belongs to -/
  typeName : String
  /-- Unique tag within the data type (0-indexed) -/
  tag : Nat
  /-- Number of fields/arguments -/
  arity : Nat
  deriving Repr, Inhabited, BEq

/-- Lookup table: constructor name → info -/
abbrev ConstructorTable := Std.HashMap String ConstructorInfo

/-- Build a ConstructorTable from the Circuit.Lower format -/
def ConstructorTable.fromLowerCtx
    (ctors : Std.HashMap String (String × Nat × Nat)) : ConstructorTable :=
  ctors.fold (init := {}) fun acc name (typeName, tag, arity) =>
    acc.insert name ⟨typeName, tag, arity⟩

/-! ## Pattern Simplification -/

/-- Context for pattern simplification -/
structure SimplifyCtx where
  /-- Constructor lookup table -/
  ctorTable : ConstructorTable

namespace SimplifyCtx

/-- Look up constructor info by name -/
def lookupCtor (ctx : SimplifyCtx) (name : String) : Option ConstructorInfo :=
  ctx.ctorTable.get? name

end SimplifyCtx

/-- Well-known tags for list-like structures -/
def listNilTag : Nat := 0
def listConsTag : Nat := 1

/-- Well-known tag for tuples (single constructor) -/
def tupleTag : Nat := 0

/-- Simplify a Metal pattern to a SimplePattern.

    Requires constructor info from the type checker to properly
    resolve constructor names to tags.
-/
partial def simplifyPattern (ctx : SimplifyCtx) : Pattern α → SimplePattern
  | .var binding name _ _ =>
    .var binding name

  | .wildcard _ _ =>
    .wildcard

  | .lit literal _ =>
    .lit literal

  | .ctor name args _ _ =>
    match ctx.lookupCtor name.display with
    | some info =>
      let simplifiedArgs := args.map (simplifyPattern ctx)
      .ctor info.tag info.arity simplifiedArgs
    | none =>
      -- Constructor not found in table - this indicates a bug in earlier phases.
      -- We use a fallback that preserves structure but may produce wrong code.
      -- In a well-typed program, this branch should never be taken.
      let simplifiedArgs := args.map (simplifyPattern ctx)
      .ctor 0 args.size simplifiedArgs

  | .tuple elems _ _ =>
    -- Tuples are single-constructor types with tag 0
    let simplifiedElems := elems.map (simplifyPattern ctx)
    .ctor tupleTag elems.size simplifiedElems

  | .array elems _ _ =>
    -- Array literals desugar to nested Cons/Nil structure
    -- [a, b, c] => Cons(a, Cons(b, Cons(c, Nil)))
    elems.foldr (init := SimplePattern.ctor listNilTag 0 #[]) fun elem acc =>
      let simplifiedElem := simplifyPattern ctx elem
      .ctor listConsTag 2 #[simplifiedElem, acc]

  | .cons head tail _ _ =>
    -- List cons pattern: Cons(head, tail)
    let simplifiedHead := simplifyPattern ctx head
    let simplifiedTail := simplifyPattern ctx tail
    .ctor listConsTag 2 #[simplifiedHead, simplifiedTail]

  | .as binding name inner _ _ =>
    let simplifiedInner := simplifyPattern ctx inner
    .as binding name simplifiedInner

  | .variant label arg _ _ =>
    -- Variant patterns use the label to determine the tag.
    -- The type checker should have resolved this to constructor info.
    -- We look up "{TypeName}.{label}" or just use label as the key.
    match ctx.lookupCtor label with
    | some info =>
      match arg with
      | none => .ctor info.tag 0 #[]
      | some p => .ctor info.tag 1 #[simplifyPattern ctx p]
    | none =>
      -- Variant label not found - same situation as unknown constructor.
      -- This is a type checking bug if it happens.
      match arg with
      | none => .ctor 0 0 #[]
      | some p => .ctor 0 1 #[simplifyPattern ctx p]

/-- Simplify a list of patterns -/
def simplifyPatterns (ctx : SimplifyCtx) (pats : Array (Pattern α))
    : Array SimplePattern :=
  pats.map (simplifyPattern ctx)

end Somac.Circuit.PatternMatch
