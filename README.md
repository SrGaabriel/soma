![GitHub branch status](https://img.shields.io/github/checks-status/SrGaabriel/soma/main?style=for-the-badge)
![GitHub Repo stars](https://img.shields.io/github/stars/SrGaabriel/soma?style=for-the-badge)
![GitHub License](https://img.shields.io/github/license/SrGaabriel/soma?style=for-the-badge)

# Soma

Soma is a dependently typed, pure functional language that compiles to native code via LLVM. It uses interaction nets as a compilation model to get deterministic, GC-free memory management without programmer annotation, reference counting, garbage collector, or explicit `free` calls.

The compiler tracks how many times each variable is used (zero, once, or many times) through Quantitative Type Theory, then inserts duplication and erasure operations at the right places. Values are copied lazily, only when both copies are actually accessed. When one side of a duplication is erased before being used, no copy happens.

---

## Language

Soma has dependent types, row polymorphism, type classes and first-class linear types. Here's what it looks like:

```lean
// Polymorphic identity
def id : ∀a. a -> a
    | x => x

// Dependent type: vector length in the type
def head {n : Nat} : Vec a (n + 1) -> a
    | Vec::Cons x _ => x

// Pattern matching on ADTs
inductive Maybe {a : Type} where
    | Nothing
    | Just (value : a)

def from_maybe {a : Type} : a -> Maybe a -> a
    | default, Maybe::Nothing => default
    | _, Maybe::Just x => x

// Row polymorphism: open record types
def get_x : { x : Int | r } -> Int
    | p => p.x

// Open variants
def to_ok (n : Int) : < Ok : Int | r >
    = .Ok n

// Type classes
class Functor (f : Type -> Type) where
    fmap : {a : Type} {b : Type} -> (a -> b) -> f a -> f b

instance : Functor Maybe where
    def fmap (g : a -> b) : Maybe a -> Maybe b
        | Maybe::Just x => Maybe::Just (g x)
        | Maybe::Nothing => Maybe::Nothing

// Linear types: use exactly once
def use_once (1 x : Int) : Int
    = x + 1
```

Quantities (`0`, `1`, `ω`) appear in binders. A `0`-bound variable is erased at compile time, generating no code. A `1`-bound variable must be used exactly once. An `ω`-bound variable (the default) can be used any number of times.

---

## Memory management

Soma has no garbage collector and no manual memory management. Memory is reclaimed deterministically through interaction net semantics baked into the compiled output.

The compiler classifies every type into two tiers:

**Flat types** (integers, booleans, floats, all-flat structs): duplication is a register copy, erasure is a no-op. Zero overhead, same as C.

**Heap types** (closures, tagged unions, recursive data): duplication creates a superposition node (SUP) that defers the copy. If only one side of the duplication is ever accessed, the SUP and its partner ERA node annihilate each other and no copy happens. If both sides are accessed, the copy happens on demand.

Defensive duplication (inserting a DUP because a value might be used in multiple branches) costs nothing when only one branch executes. The DUP and the unused ERA annihilate each other.

Soma is not Lévy-optimal. It does not share the reduction of duplicated redexes the way HVM does. The bet is that native code with good cache behavior wins over graph rewriting for most programs and that QTT eliminates most of the cases where sharing would help anyway.

---

## Getting started

Install `svm` (the Soma version manager) by cloning the repository and running:

```bash
cd svm
cargo install --path .
```

Then use the TUI to install the rest of the ecosystem:

```bash
svm tui
```

Compile a file directly:

```bash
somac <file>.soma
```

Or create and run a project:

```bash
haoma new my-project
cd my-project
haoma run
```

---

## Etymology

The name comes from three words that happen to overlap:

1. **Portuguese: "soma":** In mathematics, Σ denotes summation: the composition of many terms into a whole. Soma embraces this compositional spirit through monads chain effects. The syntax reads like notation, letting you build programs as elegant equations where complex behavior emerges from the sum of simple, pure parts.

2. **Sanskrit: सोम (soma):** In Vedic tradition, soma was a ritual drink prepared through extensive refinement: pressed, filtered and purified. The name evokes transformation through process: taking raw materials and distilling them into something potent and essential. Soma the language shares this emphasis on refinement, where high-level abstractions are transformed into efficient machine code without losing their essential clarity.

3. **Greek: σῶμα (sôma):** In Greek philosophy, sôma represents the physical embodiment of form: the material instantiation of abstract ideas. Soma gives your functional abstractions a tangible body: the compiler translates pure, high-level code into concrete, efficient executables. Just as sôma grounds the ethereal in the corporeal, Soma grounds elegant code in performant machine behavior.

---

## Acknowledgments

Thanks first to Jesus Christ for making this possible.

Thanks to **HigherOrderCo** and **Victor Taelin** for their work on interaction nets, the HVM runtime and the Interaction Calculus. Soma's Circuit IR and memory model draw directly from that research.

Thanks to the open-source community whose tools and libraries made this feasible to build.
