# The Calculus of Quantitative Constructions

A Dependent Type Theory for Practical Programming

> THIS ARTICLE IS IN REVIEW BECAUSE OF CHANGES THAT WILL BE MADE TO SOMA

---

## Abstract

The Calculus of Quantitative Constructions (CQC) is a dependent type system that combines the expressiveness of full dependent types with the practicality of quantitative (linear) type tracking. CQC serves as the core type theory for Soma, enabling a type system powerful enough for theorem proving yet ergonomic enough for everyday programming.

This document provides a complete specification of CQC: its syntax, typing rules, metatheory, and implementation strategy. We cover universes, quantities, dependent function and pair types, inductive definitions, propositional equality, row polymorphism, and the connection to interaction net execution.

---

## 1. Introduction

### 1.1 The Problem

Most dependently typed languages occupy one of two extremes:

**Theorem provers** like Coq, Agda, and Lean provide powerful type systems capable of expressing complex invariants and proving theorems. However, their totality requirements and proof obligations create friction for casual programming. Writing a simple web server in Agda requires fighting the termination checker at every turn.

**Practical languages** like Haskell, OCaml, and Rust offer excellent ergonomics for everyday programming but hit walls when stronger guarantees are needed. You cannot express "this function only accepts non-empty lists" or "this state machine follows a valid protocol" without runtime checks or external verification.

### 1.2 The CQC Approach

CQC aims for a third path: dependent types that stay out of your way until you need them.

The core insight is that by tracking *how many times* each variable is used, we can:

1. **Erase proof terms at runtime** (zero usage): Proofs exist only for type checking, then vanish.
2. **Guarantee linear resource handling** (exactly one usage): File handles, connections, and unique references.
3. **Allow normal unrestricted values** (unlimited usage): Regular programming with no restrictions.

This quantity tracking connects directly to Soma's interaction net runtime, where duplication and erasure are explicit graph operations. A proof term with quantity 0 generates no nodes. A linear handle with quantity 1 becomes a direct wire. An unrestricted value with quantity ω may generate DUP nodes for sharing.

### 1.3 Design Principles

CQC follows several guiding principles:

**Partial by default:** Unlike most dependent type theories, CQC does not require functions to terminate. Write `loop x = loop x` without a termination proof. Opt into totality with `@[total]` when you need a function to appear in types.

**Inference first:** Most code infers completely. You write `Type` and the compiler figures out `Type₀` or `Type₁`. You omit quantity annotations and the compiler infers `ω`. Annotations are for when you want guarantees, not for satisfying the type checker.

**Practical over pure:** CQC includes features like row polymorphism, mutable state (via linear types), and effects because real programs need them. Purity is a choice, not a requirement.

---

## 2. Universes

### 2.1 The Universe Hierarchy

Types themselves have types. But what is the type of `Type`?

The naive answer `Type : Type` is inconsistent. You can encode Girard's paradox, the type-theoretic analogue of Russell's paradox in set theory. Any proof becomes possible, making the type system useless for verification.

CQC uses a **predicative hierarchy** of universes:

```
Type₀ : Type₁ : Type₂ : Type₃ : ...
```

Each level `Typeᵢ` contains types whose definitions reference only lower levels. This stratification prevents self-reference and maintains consistency.

### 2.2 Universe Levels

Universe levels form a simple algebra:

```
Level ::= n           -- Concrete level (0, 1, 2, ...)
        | α           -- Level variable
        | max(L₁, L₂) -- Maximum of two levels
        | L + 1       -- Successor level
```

For function types `(x : A) → B`, if `A : Typeᵢ` and `B : Typeⱼ`, then the function type lives in `Type_{max(i,j)}`. The same rule applies to dependent pairs `(x : A) × B`.

### 2.3 Level Inference

In practice, you rarely write explicit levels. The compiler infers them:

```soma
// You write:
def id :: (a : Type) -> a -> a

// Compiler infers:
def id :: (a : Type₀) -> a -> a
// where id itself has type in Type₁
```

The inference algorithm:

1. Create fresh level variables for each `Type` without explicit level
2. Collect constraints during type checking (`α = β`, `α ≤ β`, `max(α, β) = γ`)
3. Solve constraints using iterative propagation
4. Default unsolved variables to 0 (the minimal universe)

The constraint solver handles:
- **Equality constraints:** `α = β` from unifying two types
- **Ordering constraints:** `α ≤ β` from subtyping
- **Maximum constraints:** `max(α, β) = γ` from function/pair formation

When constraints are unsatisfiable (like `0 = 1`), type checking fails with a universe inconsistency error.

### 2.4 Typical Ambiguity

For convenience, CQC supports *typical ambiguity*: you write `Type` and it means "some `Typeᵢ` that works here." The compiler picks the minimal level that satisfies all constraints.

This means you can write polymorphic functions over types without thinking about universe levels:

```soma
def const :: a -> b -> a
  | x _ => x
```

The inferred type is `(a :: Type₀) -> (b :: Type₀) -> a -> b -> a`. If you instantiate `a` or `b` with a higher-universe type, the compiler lifts everything appropriately.

---

## 3. Quantities

### 3.1 The Quantity Semiring

Every variable binding in CQC carries a *quantity* annotation describing how many times the variable may be used:

| Quantity | Symbol | Meaning |
|----------|--------|---------|
| Erased | `0` | Used zero times at runtime (type-level only) |
| Linear | `1` | Used exactly once |
| Unrestricted | `ω` | Used any number of times |

Quantities form a semiring with addition and multiplication:

**Addition** (how many times is `x` used total?):
```
0 + 0 = 0     0 + 1 = 1     0 + ω = ω
1 + 0 = 1     1 + 1 = ω     1 + ω = ω
ω + 0 = ω     ω + 1 = ω     ω + ω = ω
```

**Multiplication** (if `f` uses `x` with quantity `p` and we use `f` with quantity `q`):
```
0 × 0 = 0     0 × 1 = 0     0 × ω = 0
1 × 0 = 0     1 × 1 = 1     1 × ω = ω
ω × 0 = 0     ω × 1 = ω     ω × ω = ω
```

**Ordering** (subtyping for quantities):
```
0 ≤ 0     0 ≤ 1     0 ≤ ω
          1 ≤ 1     1 ≤ ω
                    ω ≤ ω
```

A variable declared with quantity `q` can be used with any quantity `p ≤ q`. An unrestricted variable can be used linearly or not at all. A linear variable must be used exactly once.

### 3.2 Quantity Checking

The type checker tracks variable usage throughout each expression:

```soma
def swap :: (1 p : (a, b)) -> (b, a)
  | (x, y) => (y, x)
```

Here `p` has quantity `1` (linear). The pattern match destructures it into `x` and `y`, each used exactly once. If we wrote `(y, y)`, the checker would reject it: `x` is unused and `y` is used twice.

Usage tracking handles control flow:
- **Sequential composition**: Usages add up
- **Branches** (if/case): Usages take the maximum across branches

For branches, linear variables must be used consistently. You cannot use a linear variable in one branch but not another:

```soma
def bad :: (1 h :: Handle) -> Bool -> Unit
  | h b => if b then close h else ()  -- Error: h unused in else branch
```

### 3.3 Erased Arguments

Quantity `0` marks computationally irrelevant terms. They exist for type checking but generate no runtime code:

```soma
def replicate :: (0 n :: Nat) -> (0 a :: Type) -> a -> Vec n a
```

Both `n` and `a` are erased. At runtime, `replicate` receives only the value to replicate. The type indices exist purely at compile time.

Erased terms cannot be used in runtime positions:

```soma
def bad :: (0 n : Nat) -> Nat
  | n => n + 1 // Error: using erased variable n at runtime
```

But they can be used in types (which are themselves erased):

```soma
def good :: (0 n : Nat) -> Vec n Int -> Vec (n + 1) Int
  | _ xs => cons 0 xs // OK: n appears only in types
```

### 3.4 Quantity Inference

For convenience, quantities are inferred when omitted:

```soma
// You write:
def map :: (a -> b) -> List a -> List b

// Compiler infers:
def map :: (ω f :: a -> b) -> (ω xs :: List a) -> List b
```

The default is `ω` (unrestricted) since that is what most programs need. You add explicit annotations when you want linear (`1`) or erased (`0`) semantics.

### 3.5 Connection to Interaction Nets

Quantities have direct operational meaning in Soma's interaction net runtime:

| Quantity | Interaction Net Behavior |
|----------|-------------------------|
| `0` | No nodes generated; the term is erased entirely |
| `1` | Direct wire connection; no DUP node needed |
| `ω` | May generate DUP nodes for sharing; ERA nodes for disposal |

This is the key insight that makes CQC practical. Proof terms with quantity `0` have zero runtime cost. They exist for type checking, then vanish. Linear resources with quantity `1` avoid aliasing issues without reference counting. The interaction net naturally enforces linearity through its graph structure.

---

## 4. Core Type Formers

### 4.1 Dependent Functions (Π-Types)

The dependent function type `(x : A) → B` generalizes ordinary function types. The return type `B` may mention the argument `x`:

```soma
// Non-dependent: return type doesn't mention argument
def not :: Bool -> Bool

// Dependent: return type depends on argument value
def replicate :: (n : Nat) -> a -> Vec n a
```

The formation rule:

```
Γ ⊢ A : Typeᵢ    Γ, x :ᵖ A ⊢ B : Typeⱼ
─────────────────────────────────────────
     Γ ⊢ (x :ᵖ A) → B : Type_{max(i,j)}
```

> Note: this may look scary but it's just a sequent calculus style notation. It roughly means "if in context Γ we have A of type Typeᵢ, and extending Γ with x of type A with quantity p we have B of type Typeⱼ, then the function type (x :ᵖ A) → B has type Type_{max(i,j)}." In other words again, the function type lives in the maximum universe of its domain and codomain.

Where `p` is the quantity of the parameter. Introduction (lambda) and elimination (application) follow the standard rules with quantity tracking.

**Implicit arguments** are written in braces `{x : A}` or with `@` for explicit instantiation:

```soma
def id :: {a : Type} -> a -> a
  | x => x

// Usage:
id 42         // a inferred as Int
id @Bool true // a explicitly Bool
```

### 4.2 Dependent Pairs (Σ-Types)

The dependent pair type `(x : A) × B` generalizes product types. The second component's type may depend on the first component's value:

```soma
// Non-dependent: regular pair
def pair :: (Int, String)

// Dependent: second type depends on first value
def sized :: (n : Nat) × Vec n Int
```

The formation rule:

```
Γ ⊢ A : Typeᵢ    Γ, x :ᵖ A ⊢ B : Typeⱼ
─────────────────────────────────────────
     Γ ⊢ (x :ᵖ A) × B : Type_{max(i,j)}
```

Dependent pairs express *existential quantification*: "there exists an `x : A` such that `B` holds." This is dual to dependent functions, which express *universal quantification*.

Common uses:
- **Sized collections**: `(n : Nat) × Vec n a` pairs a length with a vector of that length
- **Refinement types**: `(x : Int) × (x > 0)` pairs an integer with a proof it's positive
- **Modules/records**: First-class modules as dependent pairs

### 4.3 Inductive Types

CQC supports inductive type definitions with indices:

```soma
// Simple inductive (no indices)
data List (a : Type) where
  | Nil :: List a
  | Cons :: a -> List a -> List a

// Indexed inductive (indices affect type)
data Vec :: Nat -> Type -> Type where
  | Nil :: Vec Zero a
  | Cons :: a -> Vec n a -> Vec (Succ n) a
```

The key distinction:
- **Parameters** (like `a` in both examples) are uniform across all constructors
- **Indices** (like the `Nat` in `Vec`) can vary per constructor

Pattern matching on indexed types refines type information:

```soma
def head :: Vec (Succ n) a -> a
  | Cons x _ => x
  // No Nil case needed: the type says length ≥ 1
```

When matching on `Cons`, the type checker knows the length is `Succ n` for some `n`. The `Nil` case is impossible since it would require `Zero = Succ n`.

### 4.4 Positivity

Inductive types must satisfy the *strict positivity* condition: the type being defined cannot appear in negative (left of arrow) position in constructor arguments:

```soma
// Positive: List appears only on the right of arrows
data List a where
  | Cons :: a -> List a -> List a // OK

// Negative: Bad appears on the left of an arrow
data Bad where
  | MkBad :: (Bad -> Int) -> Bad // Error: negative occurrence
```

Negative occurrences enable encoding of paradoxes (like the Burali-Forti paradox). CQC always enforces positivity, even for non-total functions, because allowing negative types would compromise type safety.

---

## 5. Propositional Equality

### 5.1 The Equality Type

CQC includes Martin-Löf's identity type for propositional equality:

```soma
data Eq :: (a : Type) -> a -> a -> Type where
  | Refl :: Eq a x x
```

A term of type `Eq A x y` is a *proof* that `x` and `y` are equal. The only way to construct such a proof is `Refl`, which requires `x` and `y` to be definitionally equal (see Section 6).

### 5.2 Transport

Given an equality proof, we can substitute in any type-level context:

```soma
def transport :: (P : a -> Type) -> Eq a x y -> P x -> P y
  | P Refl px => px
```

Transport is the elimination principle for equality. Pattern matching on `Refl` refines the context to know `x = y`, allowing `P x` to unify with `P y`.

### 5.3 Equality Properties

From transport, we can derive the usual properties:

```soma
// Symmetry
def sym :: Eq a x y -> Eq a y x
  | Refl => Refl

// Transitivity
def trans :: Eq a x y -> Eq a y z -> Eq a x z
  | Refl Refl => Refl

// Congruence
def cong :: (f : a -> b) -> Eq a x y -> Eq b (f x) (f y)
  | f Refl => Refl
```

### 5.4 Intensional vs Extensional

CQC uses *intensional* equality: two terms are equal if they reduce to the same normal form. This is decidable since we can just normalize and compare.

The alternative, *extensional* equality, would make two functions equal if they produce equal outputs on all inputs. This is undecidable in general because of Rice's theorem.

Intensional equality has a notable limitation: function extensionality does not hold automatically:

```soma
// Cannot prove in general:
def funext :: ((x : a) -> Eq b (f x) (g x)) -> Eq (a -> b) f g
```

If you need function extensionality, you can add it as an axiom (at the cost of some computational properties) or use techniques like observational type theory.

---

## 6. Definitional Equality

### 6.1 Computation Rules

Definitional equality determines which terms the type checker considers identical without proof. CQC includes:

**β-reduction** (function application):
```
(λx. e) v ≡ e[x := v]
```

**η-expansion** (functions):
```
f ≡ λx. f x    (when f : (x : A) → B)
```

**η-expansion** (pairs):
```
p ≡ (p.1, p.2)    (when p : (x : A) × B)
```

**ι-reduction** (pattern matching):
```
case C args of { ... | C xs => e | ... } ≡ e[xs := args]
```

**δ-reduction** (unfolding definitions):
```
f ≡ body    (when f is defined as body)
```

**Primitive operations**:
```
1 + 1 ≡ 2
"hello" ++ " world" ≡ "hello world"
```

### 6.2 Row Permutation

CQC extends definitional equality with row permutation for records:

```
{ x : A, y : B } ≡ { y : B, x : A }
```

Field order in record types does not matter. This is essential for practical row polymorphism, where different code paths might construct the same record type with fields in different orders.

---

## 7. Type Checking

### 7.1 Bidirectional Type Checking

CQC uses bidirectional type checking with two modes:

**Synthesis** (`Γ ⊢ e ⇒ A`): Infer the type from the term
```
Γ ⊢ e ⇒ A    -- "e synthesizes type A"
```

**Checking** (`Γ ⊢ e ⇐ A`): Verify a term has an expected type
```
Γ ⊢ e ⇐ A    -- "e checks against A"
```

Synthesis works bottom-up: look at the term, figure out its type. Checking works top-down: we know what type we want, verify the term matches.

### 7.2 When to Synthesize vs Check

**Synthesis** is used for:
- Variables (look up in context)
- Annotated terms `(e : A)`
- Function applications (infer function type, check argument)
- Record/field access
- Literals

**Checking** is used for:
- Lambdas against function types
- Pairs against sigma types
- Pattern match bodies against expected result type
- Holes (create metavariable with expected type)

The key advantage: in checking mode, we have more information. A lambda `λx. e` alone does not tell us the type of `x`, but when checking against `(x : Int) → Bool`, we know `x : Int`.

### 7.3 Metavariables and Unification

When type information is missing, the checker creates *metavariables* (written `?α`) standing for unknown types or values:

```soma
def example = [] // Type is List ?α for some unknown α
```

Unification discovers constraints on metavariables:

```soma
def example = [1, 2, 3] // 1 : Int, so ?α = Int
```

The unification algorithm handles:
- **Pattern unification**: `?α x₁ ... xₙ = t` where `xᵢ` are distinct variables
- **Structural unification**: Recursive descent on type/term structure
- **Row unification**: Matching record/variant rows with rewriting

Constraints that cannot be solved immediately are *postponed* and retried after more information becomes available.

### 7.4 Implicit Argument Insertion

When a function expects an implicit argument, the checker automatically inserts a metavariable:

```soma
def id :: {a : Type} -> a -> a
  | x => x

def five = id 5
// Elaborates to: id @?α 5
// Then ?α = Int from unifying (5 : Int) with (x : ?α)
```

The algorithm:
1. When seeing application `f e`, infer `f`'s type
2. If the type is `{a : A} → B`, create meta `?α : A` and apply: `f @?α`
3. Continue with result type `B[a := ?α]`
4. Eventually, uses of `e` constrain `?α`

### 7.5 Greedy Constraint Solving

CQC uses a greedy approach to constraint solving:

1. Sort constraints by "difficulty" (fewer unsolved metas = easier)
2. Try to solve the easiest constraints first
3. When a meta is solved, wake up constraints that mention it
4. Iterate until fixpoint or no progress

This is not complete (some solvable constraints may be deferred forever) but works well in practice. The key insight: most constraints in real programs are simple pattern unification problems.

---

## 8. Rows and Labels

### 8.1 Row Types

CQC includes row polymorphism for flexible record and variant handling:

```soma
// Row-polymorphic field access
def getX :: { x :: a | r } -> a
  | rec => rec.x

// Works on any record with an x field
getX { x = 1, y = "hello" }  -- Int
getX { x = true, z = 42 }    -- Bool
```

A row type `{ x : A, y : B | r }` describes records with at least fields `x : A` and `y : B`, plus whatever additional fields `r` contains. The tail `r` can be:
- Another row extension: `{ z : C | s }`
- An empty row: `∅`
- A row variable: `ρ` (for polymorphism)

### 8.2 Row Operations

**Extension**: Add a field to a row
```
{ l : A | r }
```

**Field access**: Project a field from a record
```
rec.x  :  { x : A | r } → A
```

**Row unification**: Match rows up to permutation
```
{ x : A, y : B } ≈ { y : B, x : A }
```

### 8.3 Label Polymorphism

CQC supports polymorphism over field names themselves:

```soma
def getField :: (0 l :: Label) -> { l :: a | r } -> a
  | rec => rec @l

getField @x { x = 1, y = 2 }  -- 1
getField @y { x = 1, y = 2 }  -- 2
```

The label `l` has kind `Label` and quantity `0` (erased). At runtime, field access is compiled to a known offset; the label exists only for type checking.

### 8.4 Variants

Dual to records, variants (sum types) use the same row machinery:

```soma
// Variant type with two cases
def Result :: Type -> Type -> Type
  = \e a => [| Ok :: a, Err :: e |]

// Injection
def ok :: a -> Result e a = inject @Ok

// Case analysis
def handle :: Result e a -> (e -> b) -> (a -> b) -> b
  | result onErr onOk => case result of
    | Ok x => onOk x
    | Err e => onErr e
```

Row polymorphism enables extensible variants without boilerplate.

---

## 9. Totality

### 9.1 Partial by Default

Unlike most dependent type theories, CQC is *partial by default*:

```soma
// This is allowed without termination proof
def collatz :: Nat -> Nat
  | 1 => 1
  | n => if even n then collatz (n / 2)
                   else collatz (3 * n + 1)
```

Partial functions cannot appear in types (since type checking must be decidable), but they are perfectly fine for runtime code.

### 9.2 Totality Annotations

Opt into totality checking with `@[total]`:

```soma
@[total]
def add :: Nat -> Nat -> Nat
  | Zero m => m
  | Succ n m => Succ (add n m)
```

The termination checker verifies:
- All recursive calls are on structurally smaller arguments
- All pattern matches are exhaustive

Total functions can appear in types:

```soma
def concat :: Vec n a -> Vec m a -> Vec (add n m) a
```

### 9.3 Termination Checking

CQC uses structural recursion with lexicographic ordering:

1. Identify recursive calls
2. For each call, determine which arguments decrease
3. Find a lexicographic ordering that decreases on every call
4. If found, the function terminates

The checker handles nested patterns and mutual recursion. For functions that do not fit structural recursion (like quicksort), you can provide a well-founded recursion proof.

---

## 10. Instance Resolution

### 10.1 Type Classes

CQC supports type classes for ad-hoc polymorphism:

```soma
class Eq a where
  eq :: a -> a -> Bool

class Ord a where
  compare :: a -> a -> Ordering

instance Eq Int where
  eq = primIntEq

instance Ord Int where
  compare = primIntCompare
```

### 10.2 Resolution Algorithm

Instance resolution is a form of proof search:

1. Look up instances for the target class
2. For each instance, try to unify instance arguments with goal arguments
3. If matching, recursively resolve the instance's own constraints
4. Return the first fully-satisfied instance

To prevent infinite loops:
- Track active goals and detect cycles
- Limit search depth

### 10.3 Superclasses

Classes can have superclass constraints:

```soma
class Functor f where
  map :: (a -> b) -> f a -> f b

class Functor f => Applicative f where
  pure :: a -> f a
  ap :: f (a -> b) -> f a -> f b

class Applicative m => Monad m where
  bind :: m a -> (a -> m b) -> m b
```

When resolving `Monad m`, the resolver also checks for `Applicative m` and `Functor m`.

### 10.4 Instance Arguments

Instance parameters in function types are automatically resolved:

```soma
def sort :: {Ord a} -> List a -> List a
```

When calling `sort [3, 1, 2]`, the checker:
1. Infers `a = Int`
2. Creates a metavariable for the `Ord Int` instance
3. Resolves the instance using the algorithm above
4. Inserts the instance dictionary in the elaborated term

---

## 11. Relationship to Other Systems

### 11.1 Comparison with QTT (Quantitative Type Theory)

CQC is most closely related to Idris 2's Quantitative Type Theory. Both use the same quantity semiring {0, 1, ω} and similar typing rules.

Key differences:
- CQC is partial by default; QTT (as in Idris 2) requires totality
- CQC includes row polymorphism natively
- CQC's quantities connect directly to interaction net operations

### 11.2 Comparison with Traditional Dependent Types

Compared to Coq, Agda, or Lean:
- CQC allows partial functions without termination proofs
- CQC has first-class linear types (not bolted on)
- CQC lacks built-in tactics or proof automation (currently)

### 11.3 Comparison with Linear Type Systems

Compared to Linear Haskell or Rust:
- CQC integrates linearity with dependent types
- CQC's erased quantities enable zero-cost proofs
- CQC's interaction net backend gives linearity operational meaning

---

## 12. Future Directions

### 12.1 Planned Extensions

**Graded modalities**: Extend the quantity system to track other resources (memory, time, capabilities).

**Proof automation**: Tactics and decision procedures for common proof obligations.

**Refinement types**: Lightweight subset types without full dependent types.

### 12.2 Open Questions

**Extensional equality**: How to add function extensionality without breaking decidable type checking?

**Impredicativity**: Can we safely add impredicative universes for System F-style polymorphism?

**Higher inductive types**: Can we integrate HITs from Homotopy Type Theory?

---

## 13. Summary

The Calculus of Quantitative Constructions provides:

1. **Full dependent types** for expressing precise invariants
2. **Quantitative tracking** for resource management and proof erasure
3. **Partial by default** for practical programming without termination proofs
4. **Row polymorphism** for flexible record and variant handling
5. **Predicative universes** for consistent type theory
6. **Bidirectional inference** for minimal annotations
7. **Direct connection to interaction nets** for efficient compilation

The goal is a language where dependent types enhance rather than hinder programming. Most code needs no dependent features and works like a normal ML or Haskell. When you need stronger guarantees, the full power of dependent types is available without switching to a separate proof assistant.

CQC represents a synthesis of ideas from type theory (dependent types, universes), linear logic (quantities, resource tracking), and practical language design (inference, partiality, row polymorphism). The result is a type system that is both theoretically well-founded and practically usable.

---

## References

1. Martin-Löf, P. (1984). *Intuitionistic Type Theory*
2. Atkey, R. (2018). *Syntax and Semantics of Quantitative Type Theory*
3. Brady, E. (2021). *Idris 2: Quantitative Type Theory in Practice*
4. Lafont, Y. (1990). *Interaction Nets*
5. Abel, A. & Scherer, G. (2012). *On Irrelevance and Algorithmic Equality in Predicative Type Theory*
6. Geuvers, H. (1993). *Logics and Type Systems*
