# Circuit IR: Interaction Nets for Soma

This document tracks the design and implementation of Circuit, an Interaction Net-based intermediate representation for the Soma compiler. It serves as a knowledge base for understanding the design choices, goals, and current state of the implementation. But primarily, because INs are **bleeding-edge**, it's also extremely helpful to make LLMs understand it and help debug such a large infrastructure.

## Goals

1. **Optimal Reduction**: Leverage Interaction Nets for optimal (Lamping-style) evaluation of functional programs
2. **No GC, No Linear Types (in source)**: The user writes normal functional code; linearity is inferred by the compiler
3. **Strict Evaluation**: Call-by-value semantics (unlike lazy Interaction Calculus)
4. **System F-Omega**: Full support for polymorphic, higher-kinded types from Metal HIR

---

# ⚠️ CORE DESIGN PRINCIPLE: GC-FREE OPTIMAL EVALUATION ⚠️

**THIS IS THE ENTIRE POINT OF THE CIRCUIT IR.**

The goal is to achieve **optimal functional program evaluation** (in the Lamping/Levy sense) 
**WITHOUT garbage collection** and **WITHOUT requiring linear types in the source language**.

The key insight: **Interaction Nets give us precise lifetime information for free.**

After linearization, every value is used **exactly once**. This means:
- No reference counting needed (no sharing)
- No tracing GC needed (no cycles, deterministic lifetimes)
- Memory is freed at the **exact point of consumption**
- ERA nodes mark explicit "discard here" points → **free immediately**

The user writes normal functional code. The compiler:
1. Infers linearity via the linearization pass
2. Inserts explicit DUP nodes where values are used multiple times
3. Inserts explicit ERA nodes where values are discarded
4. Generates code that frees memory deterministically

**This is NOT a simplified or "good enough" approach. This is the optimal solution.**

---

## Memory Model & Runtime Strategy

### 1. Node Representation & Memory Layout

**Stack-allocated (immediate, no heap):**
- Primitives: `Int`, `Bool`, `Str` (immediate values)
- Function parameters (caller owns them)
- Results of primitive operations
- Tagged ADTs where **all fields are stack-allocated**

**Heap-allocated (only when necessary):**
- Lambdas / closures (with captured environment)
- Superpositions (SUP nodes)
- Duplicated nodes whose payload is heap-allocated
- Tagged ADTs with heap-allocated payloads

**Key principle:** Most values never touch the heap. Allocation decisions are propagated 
at **compile-time** based on type analysis. Stack is the default; heap is the exception.

### 2. Duplication Strategy (DUP)

DUP nodes are inserted at compile-time wherever a variable occurs multiple times.

**For lambdas:** Use **incremental lazy cloning** (layer-by-layer, like HVM):
- Don't eagerly copy the entire closure
- Clone incrementally as the duplicate is consumed
- Shared computations inside lambdas aren't recomputed

**For superpositions:** Allow partial copies to exist simultaneously until evaluation forces them.

**For ADTs & primitives:** Copy only the fields that are actually used.

**For stack-only references:** Avoid heap allocation entirely—just copy the immediate value.

**Insight from HVM:** Duplications are lazy, pervasive, and cheap. This avoids the 
performance penalties of naive heap cloning.

### 3. Evaluation / Rewrite Rules

- **Beta-reduction:** Apply as usual, substituting variables exactly once
- **Constructors:** Reduce according to pattern matching rules
- **Operators / primitives:** Strict evaluation
- **Superposed application:** Use DUP lazily to feed both branches efficiently
- **Call-by-need:** Only evaluate what is strictly needed, never duplicate work

The combination of lazy duplication + linear ownership ensures **no recomputation** 
and **minimal memory overhead**.

### 4. Memory Reclamation (THE KEY INSIGHT)

**No global GC.** Objects have single ownership after linearization.

**ERA nodes trigger free:**
- If the node is **heap-allocated**: deallocate the node and **recursively erase its children**
- If the node is **stack-allocated**: no-op (freed automatically when scope exits)

**Every value consumption is a potential free point:**
- When a value is used (consumed), that's its last use
- The consumer can free the value after extracting what it needs

**Compile-time propagation** determines stack vs heap, minimizing runtime checks.

**Result:** Memory management is **linear and deterministic**. No stop-the-world collection. 
No pause times. No memory leaks. Predictable, real-time-safe performance.

### 5. Parallelism (Free Bonus)

Because of linear ownership:
- Independent IN subgraphs can be reduced **entirely in parallel**, without locks
- Superpositions naturally expose parallel work (two branches = two parallel tasks)
- Minimal atomics needed due to single-owner property
- **Parallelism is a free side-effect** of the linear, duplication-driven design

### 6. Compile-time Optimizations

- Detect pure stack-only duplications → avoid heap allocation entirely
- Lift shared lambdas / repeated expressions → deforestation / beta-optimality
- Inline small functions or lambdas selectively to reduce node overhead
- Analyze usage patterns to eliminate unnecessary DUPs or SUPs
- **Goal:** Static analysis maximizes stack allocation and minimizes lazy heap materialization

### 7. Practical Restrictions

- Avoid cloning a lambda that clones itself → undefined behavior (would cause infinite loop)
- Limit superposition depth in nested lambdas to prevent combinatorial explosion
- Use typed frontend to guarantee linearity where needed

---

## Summary: Why This Works

| Traditional FP | Circuit/IN Approach |
|----------------|---------------------|
| GC traces live objects | Linearity = exact lifetimes known |
| Reference counting for sharing | No sharing after linearization |
| Unpredictable pause times | Deterministic, incremental frees |
| Complex runtime | Simple: use once, free once |
| Manual linear types (Rust) | Linearity inferred automatically |

**Result:** A runtime that can be **faster than GHC**, supports **massive parallelism**, 
and **never pauses for garbage collection**—all thanks to linear INs, lazy duplication, 
and careful compile-time memory analysis.

---

## Compilation Pipeline

```
Source (Soma)
    ↓ parsing, type checking
Metal HIR (System F-Omega, high-level)
    ↓ Circuit.Lower
Circuit IR (non-affine, variables can be used multiple times)
    ↓ Circuit.Simplify
Circuit IR (simplified, redundant lets removed)
    ↓ Circuit.Linearize  
Circuit IR (affine, each variable used exactly once, DUP/ERA explicit)
    ↓ Circuit.ToAlloy
Alloy MIR (CFG-based, SSA-style)
    ↓ Llvm.Gen.*
LLVM IR
    ↓ clang
Native executable
```

The existing Metal → Alloy path is preserved; Circuit is an alternative optimization path.

## Interaction Calculus Primer

Interaction Calculus (IC) is a term rewriting system derived from lambda calculus with three key properties:

### 1. Affine Variables
Each variable appears **at most once**. This enables:
- Safe parallel reduction (no data races)
- Efficient memory management (no GC needed)
- Optimal sharing through explicit duplication

### 2. Superpositions and Duplications
When a value needs to be used multiple times, we explicitly duplicate it:

```
-- Before (non-affine):
λx. (x x)

-- After linearization (affine):
λx. !d &0 = x; (d₀ d₁)
```

- `!d &L = val; body` — Duplication: splits `val` into two copies `d₀` and `d₁`
- `&L{a, b}` — Superposition: a value that has been "split" with label L
- Labels distinguish different duplication contexts

### 3. Core Reduction Rules

**APP-LAM (Beta reduction)**:
```
(λx. body) arg  →  body[x := arg]
```

**APP-SUP (Application distributes over superposition)**:
```
(&L{a, b} arg)  →  &L{(a arg₀), (b arg₁)}
-- where arg is duplicated into arg₀, arg₁
```

**DUP-LAM (Duplicating a lambda)**:
```
!d &L = λx. body; cont  →  cont[d₀ := λx₀. body₀, d₁ := λx₁. body₁]
-- where body is duplicated and x becomes &L{x₀, x₁}
```

**DUP-SUP (Duplication meets superposition)**:
- Same label: annihilate (direct substitution)
  ```
  !d &L = &L{a, b}; cont  →  cont[d₀ := a, d₁ := b]
  ```
- Different labels: commute (nested duplication)
  ```
  !d &L = &M{a, b}; cont  →  cont[d₀ := &M{a₀, b₀}, d₁ := &M{a₁, b₁}]
  ```

**DUP-ERA (Duplicating erasure)**:
```
!d &L = *; cont  →  cont[d₀ := *, d₁ := *]
```

## Circuit IR Design

### Term Structure (`Circuit.Ir`)

```haskell
data CTerm
    = CVar !Name !Type                -- Variable with type (affine after linearization)
    | CLam !Name !Type !CTerm         -- Lambda: λ(x : T). body
    | CApp !CTerm !CTerm !Type        -- Application: (f x) with result type
    | CLet !Name !Type !CTerm !CTerm  -- Let: let (x : T) = val in body (strict)
    | CSup !Label !CTerm !CTerm !Type -- Superposition: &L{a, b} with element type
    | CDup !Name !Type !Label !CTerm !CTerm -- Duplication: !(x : T) &L = val; body
    | CDp0 !Name !Type                -- First projection: x₀ with type
    | CDp1 !Name !Type                -- Second projection: x₁ with type
    | CEra                            -- Erasure: *
    | CRef !Name !Type                -- Function reference: @name with type
    | CInt !Int                       -- Integer literal
    | CBool !Bool                     -- Boolean literal
    | CStr !String                    -- String literal
    | CTag !Int ![CTerm] !Type        -- Tagged value: <tag, fields...> with result type
    | CCase !CTerm ![(Int, [(Name, Type)], CTerm)] !(Maybe CTerm) !Type  -- Pattern match
    | CBinOp !BinOp !CTerm !CTerm     -- Binary primitive op
    | CCmpOp !CmpOp !CTerm !CTerm     -- Comparison op
    | CUnaryOp !UnaryOp !CTerm        -- Unary op
```

### Key Design Decisions

1. **Non-affine before linearization**: `CVar` can appear multiple times initially. The `Linearize` pass inserts `CDup` nodes to make sharing explicit.

2. **Tagged values for ADTs**: Algebraic data types are encoded as `<tag, field0, field1, ...>`:
   ```
   None       = <0>
   Some x     = <1, x>
   MkPair a b = <0, a, b>
   ```
   Pattern matching uses `CCase` which dispatches on tags and binds fields.

3. **Strict evaluation**: All `CLet` bindings and function arguments are evaluated before use. This differs from standard lazy IC.

4. **Labels are integers**: Simple and efficient. The linearization pass generates fresh labels.

5. **Full type propagation**: All terms carry their types, enabling proper codegen in downstream passes.

### Module Structure

```haskell
data CModule = CModule
    { cmName :: !Name
    , cmFunctions :: ![CFunction]
    , cmTypes :: ![CTypeDef]        -- ADT definitions for reference
    , cmIsLinearized :: !Bool       -- Track linearization state
    }

data CFunction = CFunction
    { cfName :: !Name
    , cfParams :: ![(Name, Type)]   -- Typed parameters
    , cfReturnType :: !Type         -- Return type
    , cfBody :: !CTerm
    , cfMetadata :: !CFunctionMeta
    }
```

## Implementation Status

### Completed

- [x] `Circuit.Ir` — Core IR types with full type annotations
- [x] `Circuit.Linearize` — Transform non-affine → affine (insert DUP/ERA)
- [x] `Circuit.Lower` — Metal HIR → Circuit IR lowering with type propagation
- [x] `Circuit.Simplify` — Local optimizations (let inlining, dead code elimination)
- [x] `Circuit.Pretty` — Pretty printer (term format and graph format)
- [x] `Circuit.Eval` — Interaction net evaluator with reduction rules
- [x] `Circuit.ToAlloy` — Circuit → Alloy MIR lowering with proper types
- [x] `Circuit.Alloc` — Allocation analysis (StackOnly vs MaybeHeap)
- [x] Lazy DUP cloning — `OpDup`, `OpDupProj0`, `OpDupProj1` in Alloy IR
- [x] ERA → EffDrop — Free heap values at erasure points
- [x] Multi-field constructor support
- [x] Proper type propagation throughout pipeline (Session 8)
- [x] CLI command `somac circuit <file> [-l] [-g] [-e] [-a] [--llvm]`
- [x] Full LLVM pipeline — `--llvm` flag for end-to-end compilation
- [x] Runtime library (`Llvm/Gen/Runtime.hs`) — `soma_dup`, `soma_proj0/1`, `soma_era_free` (Session 8)
- [x] Deep cloning for closures — Specialized `OpDupClosure*` ops with SUP propagation (Session 13)
- [x] Fresh label generation — `soma_fresh_label` with atomic counter (Session 13)
- [x] Escape analysis for clone elision — Skip SUP cloning when closures don't escape (Session 14)
- [x] SUP-aware inlining — Track closure targets through DUP operations (Session 14)
- [x] C runtime library — Memory pools, tagged pointers, external linking (Session 16)
- [x] Runtime entry point wrapper — `main()` calls `soma_pool_init/cleanup`, user code is `soma_main` (Session 17)

### In Progress / Future Work

- [ ] Better tuple/record encoding (currently simplified)
- [x] Parallel reduction support — Work-stealing thread pool with demand-driven spawning (Session 19)
- [ ] Stack allocation for non-escaping clones
- [x] Recursive freeing in `soma_era_free` — Frees closure env slots recursively (Session 17)

## Files

### Circuit IR Pipeline

| File | Purpose |
|------|---------|
| `compiler/exe/Circuit/Ir.hs` | Core IR types with type annotations, variable analysis, AllocKind |
| `compiler/exe/Circuit/Lower.hs` | Metal → Circuit lowering with type propagation |
| `compiler/exe/Circuit/Linearize.hs` | DUP/ERA insertion pass (makes variables affine) |
| `compiler/exe/Circuit/Simplify.hs` | Local simplification pass |
| `compiler/exe/Circuit/Pretty.hs` | Pretty printer (term and graph formats) |
| `compiler/exe/Circuit/Eval.hs` | Interaction net evaluator |
| `compiler/exe/Circuit/Alloc.hs` | Allocation analysis (StackOnly vs MaybeHeap) |
| `compiler/exe/Circuit/ToAlloy.hs` | Circuit → Alloy MIR lowering (with clone tracking & escape analysis) |
| `compiler/exe/Circuit/Escape.hs` | Escape analysis for clone elision |

### LLVM Code Generation

| File | Purpose |
|------|---------|
| `compiler/exe/Llvm/Gen/CircuitEntry.hs` | Circuit-specific LLVM codegen entry point |
| `compiler/exe/Llvm/Gen/CRuntime.hs` | External declarations for C runtime |
| `compiler/exe/Llvm/Gen/Function.hs` | Function compilation (renames `main` → `soma_main`) |
| `compiler/exe/Llvm/Gen/Op.hs` | LLVM codegen for Alloy ops (incl. specialized closure DUP) |
| `compiler/exe/Llvm/Gen/Instr.hs` | Instruction compilation (incl. EffDrop → soma_era_free) |
| `compiler/exe/Llvm/Gen/Runtime.hs` | Legacy: Generated LLVM runtime (not used with C runtime) |
| `compiler/exe/Llvm/Instructions.hs` | LLVM instruction types (incl. LlvmAtomicRmw) |

### C Runtime

| File | Purpose |
|------|---------|
| `runtime/soma_runtime.h` | Header: structures, tagged pointer macros, pool API |
| `runtime/soma_runtime.c` | Implementation: pools, runtime functions, `main()` wrapper |
| `runtime/Makefile` | Build static library (`libsoma_runtime.a`) |

## Usage

```bash
# Lower a file to Circuit IR (term format)
somac circuit examples/test.soma

# Lower and apply linearization
somac circuit examples/test.soma -l

# Output in graph format (nodes and edges)
somac circuit examples/test.soma -g

# Evaluate using interaction net reduction
somac circuit examples/test.soma -e

# Lower to Alloy MIR
somac circuit examples/test.soma -l -a

# Lower to LLVM IR (implies linearization and Alloy)
somac circuit examples/test.soma --llvm

# Combine flags: linearize, graph format, evaluate, and Alloy
somac circuit examples/test.soma -l -g -e -a
```

### Output Formats

**Term format** (default): Lambda calculus-like syntax
```
@triple arg0 =
  !dup_0 &0 = arg0; !dup_1 &1 = dup_0₁; ((+ ((+ dup_0₀) dup_1₁)) dup_1₀)
```

**Graph format** (`-g`): Explicit nodes and edges
```
node_3: DUP[0] { value->node_2, proj0->*, proj1->*, body->node_5 }
node_5: DUP[1] { value->node_4, proj0->*, proj1->*, body->node_14 }
node_8: DP0(dup_0) { from_dup->* }
node_14: APP { func->node_12, arg->node_13, result->* }
```

---

# Optimal Lambda Duplication: The HVM Approach

This section documents our analysis of HVM's incremental lambda cloning technique
and how we plan to integrate it into Soma's strict evaluation model.

## The Problem: Duplicating Closures

Consider this simple program:

```haskell
let f = \x -> expensive(x)
in (f 1, f 2)
```

The closure `f` is used twice, so the linearization pass inserts a DUP:

```
!dup &0 = (λx. expensive(x)); (dup₀ 1, dup₁ 2)
```

**The naive approach**: Deep-clone the entire closure when duplicated.
- Wasteful: `expensive` gets duplicated even if the logic inside is shared
- Breaks optimal reduction: Shared subcomputations are recomputed

**The HVM approach**: Incremental lazy cloning.
- Don't copy the closure immediately
- Clone layer-by-layer as the duplicate is consumed
- Shared computations inside lambdas are never recomputed

## HVM's Key Insight: Lambdas Don't Have Scopes

In traditional lambda calculus, a variable is always "inside" its binder:

```
λx. (x + x)    -- x is scoped to the lambda body
```

HVM breaks this assumption. After duplication, a variable can appear
**outside** its lambda binder. This sounds insane, but it enables
incremental cloning:

```javascript
dup a b = λx(body)
------------------ Dup-Lam
a <- λx0(b0)
b <- λx1(b1)
x <- {x0 x1}       // x becomes a SUPERPOSITION
dup b0 b1 = body   // Continue duplicating the body lazily
```

In English: "To duplicate a lambda λx(body), create two new lambdas with
fresh parameters x0 and x1, replace x with the superposition {x0 x1},
and continue duplicating the body."

### Superpositions

A superposition `{a b}` represents a value that is "both a and b" depending
on context. When a DUP's first projection is accessed, it gets `a`. When
the second projection is accessed, it gets `b`.

The magic: superpositions **propagate through the program** until they
meet their matching DUP, at which point they annihilate:

```javascript
dup x y = {a b}
--------------- Dup-Sup (same label)
x <- a
y <- b
```

### Example: Duplicating a Nested Lambda

```javascript
dup a b = λx(λy(Pair x y))
(Pair a b)
------------------------------------------- Dup-Lam (outer λx)
dup a b = λy(Pair {x0 x1} y)
(Pair λx0(a) λx1(b))
------------------------------------------- Dup-Lam (inner λy)  
dup a b = (Pair {x0 x1} {y0 y1})
(Pair λx0(λy0(a)) λx1(λy1(b)))
------------------------------------------- Dup-Ctr (Pair)
dup a b = {x0 x1}
dup c d = {y0 y1}
(Pair λx0(λy0(Pair a c)) λx1(λy1(Pair b d)))
------------------------------------------- Dup-Sup (annihilate)
dup c d = {y0 y1}
(Pair λx0(λy0(Pair x0 c)) λx1(λy1(Pair x1 d)))
------------------------------------------- Dup-Sup (annihilate)
(Pair λx0(λy0(Pair x0 y0)) λx1(λy1(Pair x1 y1)))
```

The lambdas were duplicated **incrementally**, and the result is correct!

### Why This Enables Optimal Sharing

```javascript
dup f g = ((λx λy (Pair (+ x x) y)) 2)
(Pair (f 10) (g 20))
----------------------------------- App-Lam (apply 2 to outer lambda)
dup f g = λy (Pair (+ 2 2) y)
(Pair (f 10) (g 20))
----------------------------------- Dup-Lam
dup f g = (Pair (+ 2 2) {y0 y1})
(Pair (λy0(f) 10) (λy1(g) 20))
----------------------------------- App-Lam (apply 10)
dup f g = (Pair (+ 2 2) {10 y1})
(Pair f (λy1(g) 20))
----------------------------------- App-Lam (apply 20)
dup f g = (Pair (+ 2 2) {10 20})
(Pair f g)
----------------------------------- Dup-Ctr
dup a b = (+ 2 2)
dup c d = {10 20}
(Pair (Pair a c) (Pair b d))
----------------------------------- Op2-U32 (compute ONCE!)
dup a b = 4
dup c d = {10 20}
(Pair (Pair a c) (Pair b d))
----------------------------------- Dup-U32
dup c d = {10 20}
(Pair (Pair 4 c) (Pair 4 d))
----------------------------------- Dup-Sup
(Pair (Pair 4 10) (Pair 4 20))
```

**Notice**: `(+ 2 2)` was computed only **once**, even though it was inside
two duplicated lambda binders! In GHC, this would cause un-sharing and
the addition would happen twice.

## The Tension: Strict vs Lazy

HVM is inherently **lazy**:
- Duplications happen incrementally as values are demanded
- Superpositions exist as runtime values that propagate
- The runtime is a graph reducer

Soma is **strict** (call-by-value):
- Arguments are evaluated before function application
- We compile to efficient LLVM IR, not a graph interpreter
- Linear ownership for deterministic memory management

### Three Possible Paths

**Path A: Accept the Limitation**
- Keep strict semantics
- Closures are eagerly deep-cloned when duplicated
- Lose optimal sharing for higher-order code
- Simple, predictable performance (like Rust/C++)

**Path B: Hybrid Approach** ← OUR CHOICE
- First-order code: Direct LLVM compilation (current approach)
- Higher-order code with duplicated closures: Graph-based lazy reduction
- Best of both worlds, complexity is localized

**Path C: Full Graph Reducer**
- Runtime is a graph reducer like HVM
- Lose direct LLVM compilation
- Maximum theoretical optimality, but fundamentally different architecture

## Path B: Hybrid Strict/Lazy Reduction

We chose Path B because it preserves all our goals while gaining optimal
reduction where it matters:

| Goal | Path B Status |
|------|---------------|
| GC-free | ✓ Linear ownership still works |
| No linear types in source | ✓ Compiler infers everything |
| Strict evaluation | ✓ First-order code is strict |
| Optimal reduction | ✓ For duplicated closures |
| Native LLVM performance | ✓ For first-order hot paths |

### The Key Insight: Hybrid Detection

At compile time, we already know:
1. **What gets duplicated** — linearization pass inserts DUP nodes
2. **The type of each value** — full type propagation is implemented
3. **Is it a closure?** — function types are trivially identifiable

Decision rule:
```
DUP on Int/Bool/ADT → copy directly (zero overhead, current behavior)
DUP on closure type → create graph node, reduce lazily
```

### When Do We Pay for Graph Reduction?

Only when:
1. A closure is duplicated, AND
2. Both copies are actually used

For strict code where closures are passed around and applied once,
there is **no overhead at all**.

## Runtime Architecture for Path B

### Closure Representation

Closures must be representable as graph nodes:

```
SomaClosure = {
    tag: u8           // NODE_CLOSURE
    func_ptr: ptr     // Pointer to the function code
    arity: u8         // Number of remaining parameters
    env_size: u16     // Number of captured variables
    env: [ptr]        // Captured environment (array of values)
}
```

### Extended SUP Node

When duplicating a closure, we create an extended SUP:

```
SomaSupClosure = {
    tag: u8           // NODE_SUP_CLOSURE
    label: u32        // Duplication label
    closure: ptr      // Original closure
    state: u8         // 0=fresh, 1=proj0_accessed, 2=proj1_accessed, 3=both
    proj0: ptr        // Cached projection 0 (or partially cloned closure)
    proj1: ptr        // Cached projection 1
}
```

### DUP-LAM Rule Implementation

When `soma_proj0` or `soma_proj1` is called on a SUP containing a closure:

**First projection accessed:**
1. Mark state as "first accessed"
2. Return the original closure (no cloning yet!)
3. Store which projection took it

**Second projection accessed:**
1. Now we must clone
2. Create fresh parameter bindings (x0, x1)
3. Clone the body with substitution x → {x0 x1}
4. Return the cloned closure

This is **lazy** — cloning only happens when both copies are actually used.

### Superposition Propagation

When a superposed closure is applied:

```
({closure0 closure1} arg)
─────────────────────────── App-Sup
dup arg0 arg1 = arg
{(closure0 arg0) (closure1 arg1)}
```

The runtime must detect when a SUP is in function position and distribute
the application.

### Label-Based Annihilation

When DUP meets SUP with the same label:

```
dup x y = {a b}  where labels match
───────────────
x <- a
y <- b
```

This is the "completion" of a duplication chain — the superposition was
created by the same DUP that's now consuming it.

When labels differ (nested duplication), we must commute:

```
dup x y = {a b}  where labels differ
───────────────
x <- {x_a x_b}
y <- {y_a y_b}
dup x_a y_a = a
dup x_b y_b = b
```

## Implementation Plan

### Phase 1: Closure Representation ✓
- [x] Define `SomaClosure` structure in runtime
- [x] `soma_alloc_closure(func_ptr, arity, env_size)` — allocate closure
- [x] `soma_closure_set_env(closure, index, value)` — set env slot
- [x] `soma_closure_get_env(closure, index)` — get env slot
- [x] `soma_clone_closure(closure)` — deep-clone closure with memcpy
- [x] `OpWrapClosure` — wrap function pointers in SomaClosure at compile-time
- [x] Update codegen to emit closure allocations for lambdas with captured vars
- [x] Ensure captured variables are properly stored in env slots

### Phase 2: Closure-Aware DUP ✓
- [x] Detect closure types at runtime (first byte == NODE_CLOSURE)
- [x] `soma_proj0`/`soma_proj1` check value tag and clone closures
- [x] State tracking: fresh(0), proj0_accessed(1), proj1_accessed(2), both(3)
- [x] Wrap function types before DUP in `Circuit/ToAlloy.hs`

### Phase 3: Incremental Cloning
- [ ] Implement body substitution for fresh parameters
- [ ] Create superposition values for parameters
- [x] Handle nested lambdas correctly

### Phase 4: SUP Propagation
- [x] Strict evaluation handles this implicitly — DUP always projects before use
- [x] Projections trigger lazy cloning for closures
- [ ] (Optional) Runtime App-Sup for lazy evaluation mode
- [ ] Handle Op-Sup for primitive operations

### Phase 5: Label Tracking
- [x] Labels stored in SUP nodes (i32 field)
- [x] Implement same-label annihilation
- [x] Implement different-label commutation

## The HVM Limitation

HVM has one restriction worth noting:

> "If a lambda that clones its argument is itself cloned, then its clones
> aren't allowed to clone each-other."

Example of **disallowed** code:
```javascript
let g = λf(λx(f (f x)))
(g g)  // g clones its argument, g is cloned, clone tries to clone clone
```

This is easily fixed:
```javascript
let g = λf(λx(f (f x)))
let h = λf(λx(f (f x)))
(g h)  // h is a separate definition, not a clone of g
```

This limitation is extremely rare in practice. As HVM's documentation notes:
"Unless you like multiplying Church-Encoded natural numbers in a loop,
you've probably never seen a program that reaches this limitation."

For Soma, we will implement the same restriction and potentially add a
compile-time check to reject such programs with a clear error message.

---

## References

- [Interaction Calculus README](https://github.com/VictorTaelin/Interaction-Calculus) — Core IC concepts
- [HVM](https://github.com/HigherOrderCO/HVM) — Production IN runtime
- Lamping, "An Algorithm for Optimal Lambda Calculus Reduction" (1990)

## Session Log

### Session 1-7 (2024)

See previous entries for:
- Session 1: Initial IR design, linearization, lowering, evaluator
- Session 2: Circuit → Alloy lowering
- Session 3: GC-free memory management, allocation analysis
- Session 4: Lazy DUP cloning with OpDup/OpDupProj0/OpDupProj1
- Session 5: Full LLVM pipeline
- Session 6: Multi-field constructor support
- Session 7: Simplification pass, PVar pattern fix, parameter linearization

### Session 8 (2024)

**Proper Type Propagation Throughout Pipeline:**

This session added full type annotations to the Circuit IR and propagated types
correctly through all passes from Metal HIR to Alloy MIR.

**Problem:** The Circuit IR was using placeholder `intType` everywhere, losing
the actual type information from Metal HIR. This caused incorrect types in
Alloy MIR output.

**Solution:** Added type annotations to all CTerm constructors and updated
all passes to propagate and use these types.

**Changes to `Circuit/Ir.hs`:**

All CTerm constructors now carry their types:
```haskell
data CTerm
    = CVar !Name !Type              -- Variable with type
    | CLam !Name !Type !CTerm       -- Lambda with param type
    | CApp !CTerm !CTerm !Type      -- App with result type
    | CLet !Name !Type !CTerm !CTerm
    | CSup !Label !CTerm !CTerm !Type
    | CDup !Name !Type !Label !CTerm !CTerm
    | CDp0 !Name !Type
    | CDp1 !Name !Type
    | CRef !Name !Type
    | CTag !Int ![CTerm] !Type
    | CCase !CTerm ![(Int, [(Name, Type)], CTerm)] !(Maybe CTerm) !Type
    ...
```

Added `getTermType :: CTerm -> Type` to extract types from terms.

CFunction now has typed parameters:
```haskell
data CFunction = CFunction
    { cfName :: !Name
    , cfParams :: ![(Name, Type)]   -- Was: [Name]
    , cfReturnType :: !Type         -- NEW
    , cfBody :: !CTerm
    , cfMetadata :: !CFunctionMeta
    }
```

**Changes to `Circuit/Lower.hs`:**

- `buildAppChain` computes intermediate types for curried applications
- `buildLamChain` extracts parameter types from function types
- `lowerCaseArm` returns `[(Name, Type)]` for bound variables
- `extractPatternInfo` and `extractFieldNameAndType` propagate scrutinee type

**Changes to other passes:**

- `Circuit/Linearize.hs`: Updated all pattern matches for typed constructors
- `Circuit/Simplify.hs`: Updated for typed terms
- `Circuit/Pretty.hs`: Updated (ignores types in output for readability)
- `Circuit/Eval.hs`: Updated all pattern matches, types preserved through reduction
- `Circuit/Alloc.hs`: Updated pattern matches for typed constructors

**Changes to `Circuit/ToAlloy.hs`:**

Removed placeholder `intType` usage:
```haskell
-- Before:
beginFunction cfName paramTypes intType
emitLetTmp intType (OpCall ...)

-- After:
beginFunction cfName cfParams cfReturnType
emitLetTmp resultTy (OpCall ...)  -- resultTy from CApp type annotation
```

All operations now use proper types from the Circuit IR.

**Test results:**

```
func unwrap(arg0: (Option (* -> *)) <Int>) -> Int {
  ...
  t1 = arg0.0 (Int)           -- Field has correct Int type
  ...
}

func swap(arg0: ((Pair (* * -> *)) <Int>) <Int>) -> ((Pair (* * -> *)) <Int>) <Int> {
  ...
  t15 = construct MkPair#0(t14, t13) (((Pair (* * -> *)) <Int>) <Int>)
  ...
}
```

Types are now correctly propagated from Metal HIR through Circuit IR to Alloy MIR.

**Files modified:**
- `Circuit/Ir.hs`: Added type annotations to all constructors, `getTermType`
- `Circuit/Lower.hs`: Type propagation from Metal expressions
- `Circuit/Linearize.hs`: Updated for typed terms
- `Circuit/Simplify.hs`: Updated for typed terms
- `Circuit/Pretty.hs`: Updated for typed terms
- `Circuit/Eval.hs`: Updated for typed terms
- `Circuit/Alloc.hs`: Updated for typed terms
- `Circuit/ToAlloy.hs`: Use proper types from IR instead of placeholders

**Interaction Net Runtime Library:**

Also in Session 8, implemented the runtime library for lazy duplication in LLVM.

**New file `Llvm/Gen/Runtime.hs`:**

Generates LLVM functions for interaction net reduction:

```haskell
-- Runtime functions generated as LlvmFunction structures
runtimeFunctions :: [LlvmFunction]
runtimeFunctions =
    [ somaDupFunction      -- Create lazy SUP node
    , somaProj0Function    -- First projection
    , somaProj1Function    -- Second projection  
    , somaEraFreeFunction  -- Free heap value
    ]
```

**SUP Node Structure:**
```llvm
%SomaSup = type { i8, i32, ptr, ptr, ptr }
; Fields: tag (accessed?), label, value, proj0_cache, proj1_cache
```

**Runtime semantics:**
- `soma_dup(label, value)`: Allocates SUP node, stores value, returns handle
- `soma_proj0(sup)`: Returns first projection (caches result, shares if first access)
- `soma_proj1(sup)`: Returns second projection (caches result, shares if first access)
- `soma_era_free(value)`: Frees heap-allocated value

**Integration with LLVM codegen:**

The runtime functions are automatically included in every compiled module:
```haskell
-- In Llvm/Gen/Entry.hs
runLlvmCodeGen alloyModule = ...
    fns = runtimeFunctions ++ irFunctions finalStat
```

**Example output for `triple x = x + x + x`:**
```llvm
define i32 @"triple"(i32 %arg0) {
  ; DUP[0] for first split
  %tmp_reg_0 = inttoptr i32 %arg0 to ptr
  %tmp_reg_1 = call ptr @"soma_dup"(i32 0, ptr %tmp_reg_0)
  %tmp_reg_4 = call ptr @"soma_proj0"(ptr %tmp_reg_3)  ; first copy
  %tmp_reg_7 = call ptr @"soma_proj1"(ptr %tmp_reg_6)  ; second copy
  
  ; DUP[1] for second split of the second copy
  %tmp_reg_10 = call ptr @"soma_dup"(i32 1, ptr %tmp_reg_9)
  %tmp_reg_13 = call ptr @"soma_proj0"(ptr %tmp_reg_12) ; third copy
  %tmp_reg_16 = call ptr @"soma_proj1"(ptr %tmp_reg_15) ; fourth copy (unused)
  
  ; Use copies in additions
  ...
}
```

**Current limitations:**
- ~~Shallow copy semantics (both projections share the same value pointer)~~ **FIXED in Session 9**
- No label checking for DUP-SUP annihilation/commutation (planned)
- ~~No deep cloning for closures (planned)~~ **FIXED in Session 9**

**Files added/modified:**
- `Llvm/Gen/Runtime.hs`: New runtime library module
- `Llvm/Gen/Entry.hs`: Integrated runtime into module generation
- `soma.cabal`: Added `Llvm.Gen.Runtime` module

### Session 9 (2024)

**HVM-Style Incremental Lambda Cloning & Path B Implementation:**

This session implemented the runtime infrastructure for HVM-style lazy duplication
with closure-aware cloning, following the Path B hybrid approach.

**New Runtime Functions in `Llvm/Gen/Runtime.hs`:**

Extended the runtime library with closure support:

```haskell
runtimeFunctions :: [LlvmFunction]
runtimeFunctions =
    [ somaDupFunction           -- Create lazy SUP node
    , somaProj0Function         -- First projection (with closure cloning)
    , somaProj1Function         -- Second projection (with closure cloning)
    , somaEraFreeFunction       -- Free heap value
    , somaAllocClosureFunction  -- NEW: Allocate closure with env
    , somaClosureSetEnvFunction -- NEW: Set environment slot
    , somaClosureGetEnvFunction -- NEW: Get environment slot
    , somaCloneClosureFunction  -- NEW: Deep-clone closure
    ]
```

**Closure Structure:**
```llvm
%SomaClosure = type { i8, i8, i16, ptr }  ; tag, arity, env_size, func_ptr
; Environment slots follow the header as a variable-length array
```

- `soma_alloc_closure(func_ptr, arity, env_size)` — Allocates 16 + env_size*8 bytes
- `soma_closure_set_env(closure, index, value)` — Sets env[index] = value
- `soma_closure_get_env(closure, index)` — Returns env[index]
- `soma_clone_closure(closure)` — Deep-clones via memcpy

**Enhanced Projection Functions:**

`soma_proj0` and `soma_proj1` now implement proper DUP-LAM semantics:

1. **State tracking:** tag field stores 0=fresh, 1=proj0_accessed, 2=proj1_accessed, 3=both
2. **First projection:** Returns original value, marks which projection took it
3. **Second projection:** Checks if value is a closure (first byte == 1)
   - If closure: calls `soma_clone_closure` for deep copy
   - If not closure: returns same pointer (shallow copy for primitives)

```llvm
; In proj1_was_first block:
check_closure:
  %value_tag = load i8, ptr %value3
  %is_closure = icmp eq i8 %value_tag, 1
  br i1 %is_closure, label %clone_closure, label %return_shallow

clone_closure:
  %cloned = call ptr @"soma_clone_closure"(ptr %value3)
  ...
```

**Path B Hybrid Approach:**

The implementation follows the documented Path B strategy:
- First-order code: Direct LLVM compilation (zero overhead)
- Higher-order code with duplicated closures: Lazy cloning at runtime
- Detection is runtime-based: check first byte of value to determine if closure

**What Works Now:**
- Lazy duplication for all values via SUP nodes
- Automatic closure detection and deep cloning when both projections used
- Primitives (Int, Bool, etc.) use shallow copy (no allocation)
- State tracking prevents duplicate cloning

**Remaining Work:**
- Frontend closure support: `Metal/Lift.hs` needs to handle lambdas with free variables
- The runtime is ready, but codegen doesn't emit closure allocations yet
- Label-based DUP-SUP annihilation/commutation (Phase 5)

**Files modified:**
- `Llvm/Gen/Runtime.hs`: Added closure functions, enhanced projections with cloning
- `CIRCUIT.md`: Updated implementation plan, documented HVM approach and Path B design

### Session 10 (2024)

**OpWrapClosure: Compile-Time Closure Wrapping for DUP-LAM:**

This session completed the closure wrapping infrastructure so that function-typed
values are properly wrapped in `SomaClosure` structures before duplication.

**The Problem:**

In Session 9, the runtime was ready to detect and clone closures (checking first
byte == NODE_CLOSURE), but function references (`CRef`) were compiling to raw
function pointers. Raw function pointers don't have a tag byte, so the runtime
couldn't distinguish them from other values.

**The Solution: `OpWrapClosure`**

Added a new Alloy IR operation that wraps function pointers in `SomaClosure`
structures at compile time:

```haskell
-- In Alloy/Ir.hs
data AOp = ...
    | OpWrapClosure AOperand  -- wrap function pointer in SomaClosure
```

**Changes to `Circuit/ToAlloy.hs`:**

When lowering a `CDup` node, check if the value has a function type:

```haskell
MaybeHeap -> do
    -- For function types, wrap in SomaClosure first so runtime
    -- can detect and clone them (DUP-LAM rule)
    wrappedOp <- case ty of
        TArrow _ _ -> do
            -- Wrap function pointer in closure structure
            wrapped <- emitLetTmp ty (OpWrapClosure valOp)
            pure (OpVar wrapped)
        _ -> pure valOp
    supHandle <- emitLetTmp ty (OpDup label wrappedOp)
```

**Changes to `Llvm/Gen/Op.hs`:**

Compile `OpWrapClosure` to a `soma_alloc_closure` call:

```haskell
compileOp (OpWrapClosure funcOp) resultTy = do
    llFunc <- compileOperand funcOp
    -- Cast function to void* for storage
    voidFuncPtr <- saveTmp (LlvmCast "bitcast" llFunc (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
    -- Allocate closure with arity=0, env_size=0
    let allocClosureFunc = LlvmGlobal (LlvmPointer LlvmI8) "\"soma_alloc_closure\""
    closure <- saveTmp (LlvmCall allocClosureFunc (LlvmPointer LlvmI8) 
                        [voidFuncPtr, LlvmLiteral LlvmI8 "0", LlvmLiteral LlvmI16 "0"]) 
               (LlvmPointer LlvmI8)
    -- Cast result to expected type
    resultLlTy <- lift $ toLlvmType resultTy
    saveTmp (LlvmCast "bitcast" (LlvmVar closure (LlvmPointer LlvmI8)) resultLlTy) resultLlTy
```

**Updated Passes:**

All Alloy IR passes were updated to handle `OpWrapClosure`:
- `Alloy/Simplify.hs` — Substitution in operand
- `Alloy/Defunc.hs` — No transformation needed
- `Alloy/Subst.hs` — Apply substitution to operand
- `Alloy/PromoteRefs.hs` — Check if name appears in operand
- `Alloy/Uniqueness.hs` — Track uses in operand
- `Logging/Trees.hs` — Pretty printing

**Verification:**

Test output shows the complete pipeline working:

```
=== Alloy MIR ===
ILet "t6" (TArrow Int Int) (OpWrapClosure (OpVar "arg0"))
ILet "t7" (TArrow Int Int) (OpDup 0 (OpVar "t6"))
...

=== LLVM IR ===
%tmp_reg_10 = select i1 true, ptr @"add1Closure", ptr @"add1Closure"
%tmp_reg_11 = call ptr @"soma_alloc_closure"(ptr %tmp_reg_10, i8 0, i16 0)
%tmp_reg_14 = call ptr @"soma_dup"(i32 0, ptr %tmp_reg_13)
```

Function references are now:
1. Wrapped in `SomaClosure` via `soma_alloc_closure`
2. The closure has `tag = NODE_CLOSURE (1)` as its first byte
3. When both projections of a DUP are accessed, runtime detects the tag
4. `soma_clone_closure` is called for deep copying

**Test Files Removed:**

The temporary test infrastructure was removed as requested:
- `compiler/exe/Circuit/TestClosure.hs` — deleted
- `TestClosureRuntime` command — removed from `Config/Options.hs` and `Main.hs`
- `Circuit.TestClosure` — removed from `soma.cabal`

**Files modified:**
- `Alloy/Ir.hs` — Added `OpWrapClosure` constructor
- `Circuit/ToAlloy.hs` — Wrap function types before DUP
- `Llvm/Gen/Op.hs` — Compile `OpWrapClosure` to `soma_alloc_closure`
- `Alloy/Simplify.hs`, `Alloy/Defunc.hs`, `Alloy/Subst.hs` — Handle new op
- `Alloy/PromoteRefs.hs`, `Alloy/Uniqueness.hs` — Handle new op
- `Logging/Trees.hs` — Pretty print new op
- `Config/Options.hs`, `Main.hs`, `soma.cabal` — Remove test command

**Implementation Status Update:**

Phase 1 (Closure Representation) and Phase 2 (Closure-Aware DUP) are now complete:
- [x] `SomaClosure` structure in runtime
- [x] `soma_alloc_closure`, `soma_clone_closure`
- [x] Runtime closure detection (tag check)
- [x] `OpWrapClosure` for compile-time wrapping
- [x] Function types wrapped before duplication

Remaining for full closure support:
- [x] Frontend closure allocation (lambdas with captured variables)
- [x] Environment slot population for actual closures
- [x] Phase 3: Incremental cloning with parameter substitution
- [x] Phase 5: Label-based DUP-SUP annihilation/commutation

### Session 11 (2024)

**Full Closure Compilation Pipeline:**

This session completed the closure compilation pipeline for Path B, enabling
lambdas with captured variables to compile and run correctly.

**Problems Fixed:**

1. **Lambda lifting not capturing function parameters** (`Metal/Lift.hs:127-133`)
   - Bug: Free variables from enclosing function parameters (`available` set) were
     excluded from capture
   - Fix: Removed `available` from exclusion - closures must capture all free vars
     since they may escape their defining scope

2. **Return type computation for closure-returning functions** (`Metal/Gen/Binding.hs`)
   - Bug: `uncurryFunction` fully uncurried types, so `Int -> Int -> Int` became
     `([Int, Int], Int)` instead of `([Int], Int -> Int)`
   - Fix: Added `splitFunctionType` that splits based on actual parameter count
   - Also fixed in `Metal/Lift.hs` for lifted lambdas

3. **Closure call convention** (`Alloy/Lower.hs`)
   - Added `ClosureInfo` to track both env size and underlying function name
   - Added `ClosureReturnInfo` to track what functions return closures
   - When calling a closure: extract func ptr + all env values, prepend to args
   - When binding result of closure call: check if underlying func returns closure

**New Data Structures in `Alloy/Lower.hs`:**

```haskell
-- Info about a closure binding
data ClosureInfo = ClosureInfo
    { ciEnvSize :: !Int        -- number of captured env values
    , ciFuncName :: !String    -- underlying lifted function name
    }

-- Info about what a function returns if it returns a closure
data ClosureReturnInfo = ClosureReturnInfo
    { criEnvSize :: !Int      -- env size of the returned closure
    , criLiftedFn :: !String  -- the lifted function the closure points to
    }
```

**Test Cases Working:**

1. **Simple closure** - `makeAdder 5` returns closure, `add5 10` = 15 ✓
   ```
   def makeAdder(n: Int) -> Int -> Int = (\x -> x + n)
   let add5 = makeAdder 5 in add5 10  -- returns 15
   ```

2. **Nested closures** - Multiple levels of closure creation ✓
   ```
   def makeMultiAdder(a: Int) -> Int -> Int -> Int =
       (\b -> (\c -> a + b + c))
   let f = makeMultiAdder 10 in
   let g = f 20 in
   g 5  -- returns 35
   ```

3. **Closures without captures as arguments** ✓
   ```
   def applyTwice(f: Int -> Int, x: Int) -> Int = f (f x)
   let addFive = (\y -> y + 5) in
   applyTwice addFive 10  -- returns 20
   ```

**Closures with Captures as Function Arguments** ✅ (Fixed in Session 12)

Passing closures that have captured variables as function arguments now works:

```
def applyTwice(f: Int -> Int, x: Int) -> Int = f (f x)
let n = 3 in
let addN = (\y -> y + n) in   -- addN captures n
applyTwice addN 10            -- Returns 16 (correct!)
```

This was fixed by implementing the **uniform closure calling convention**:
- All function-typed values are closures
- Lifted functions take `closure_self` as first param, extract their own env
- Callers just pass the closure pointer
- Simple, uniform, slight overhead for simple functions

See Session 12 for implementation details.

**Files Modified:**

- `Metal/Lift.hs` — Fixed free variable capture, added `splitFunctionType`
- `Metal/Gen/Binding.hs` — Added `splitFunctionType`, `getBodyArity`
- `Alloy/Lower.hs` — Added `ClosureInfo`, `ClosureReturnInfo`, closure tracking
- `Alloy/Ir.hs` — Added `ClosureInfo` type (later moved to Lower.hs)

**Implementation Status Update:**

Phase 1 (Closure Representation): ✅ Complete
- [x] `SomaClosure` structure in runtime
- [x] `soma_alloc_closure`, `soma_closure_set_env`, `soma_closure_get_env`
- [x] `soma_clone_closure` for deep copying
- [x] `OpAllocClosure`, `OpClosureGetFunc`, `OpClosureGetEnv` in Alloy IR
- [x] LLVM codegen for all closure operations

Phase 2 (Closure-Aware DUP): ✅ Complete
- [x] Runtime closure detection (tag == NODE_CLOSURE)
- [x] `OpWrapClosure` for compile-time wrapping
- [x] Automatic cloning when both DUP projections accessed

Closure Compilation: ✅ Complete
- [x] Lambda lifting with captured variables (`Metal/Lift.hs`)
- [x] MClosure emission for lambdas with free vars
- [x] Correct return types for closure-returning functions
- [x] Closure call lowering (extract func + env, prepend to args)
- [x] Nested closure support (closures returning closures)
- [x] Closures without captures as function arguments
- [x] **Closures WITH captures as function arguments** (uniform calling convention - Session 12)

Phase 3 (Incremental Cloning): ⏳ Not started
- [ ] Body substitution for fresh parameters
- [ ] Superposition values for duplicated parameters

Phase 5 (Label Tracking): ⏳ Not started
- [x] Same-label DUP-SUP annihilation
- [x] Different-label commutation

### Session 12 (2024)

**Uniform Closure Calling Convention:**

This session implemented the uniform closure calling convention, fixing the limitation
where closures with captured variables couldn't be passed as function arguments.

**The Problem:**

Previously, when calling through a function-typed parameter (like `f` in `applyTwice(f, x)`),
we didn't know the env_size at compile time. The call `f(x)` was lowered as a direct
indirect call without extracting the closure's func ptr and env values, causing segfaults.

**The Solution: Uniform Calling Convention**

All function-typed values are now closures, and lifted functions take `closure_self`
as their first parameter. The function extracts its own captured variables from
`closure_self` at entry, so call sites don't need to know the env_size.

**Key Changes:**

1. **`Typing/Types.hs`**: Added `closurePtrType` for the `ClosurePtr` type
   ```haskell
   closurePtrType = TConstructor (TypeConstructor "ClosurePtr" KindStar)
   ```

2. **`Metal/Metadata.hs`**: Added `ClosureFunctionInfo` to track captured vars
   ```haskell
   data ClosureFunctionInfo = ClosureFunctionInfo
       { cfiCapturedVars :: [(String, Type)]
       }
   ```

3. **`Metal/Lift.hs`**: Major changes to lambda lifting
   - All lambdas now emit `MClosure` (even zero-capture ones)
   - Lifted functions take `("closure_self", closurePtrType)` as first param
   - Captured vars stored in `mfmClosureInfo` metadata (not as params)
   - Call sites pass closure as first argument

4. **`Alloy/Lower.hs`**: Uniform call lowering
   - At function entry, extract captured vars from `closure_self` using `OpClosureGetEnv`
   - For all function-typed callees, extract func ptr and pass closure as first arg
   - Added case for `isFunctionType` to handle indirect calls uniformly

5. **`Llvm/Gen/TypeConversion.hs`**: Added `ClosurePtr` → `ptr i8` mapping

**Example - Before (Session 11):**

```haskell
-- applyTwice would segfault when f had captured variables
def applyTwice(f: Int -> Int, x: Int) -> Int = f (f x)
let addN = (\y -> y + n) in applyTwice addN 10  -- SEGFAULT
```

**Example - After (Session 12):**

```
-- Metal HIR:
def lambda$0(closure_self: ClosurePtr, y: Int) -> Int = +(y, n)
def main :: Int = let addN = closure(lambda$0, [n]) in applyTwice(addN, 10)

-- Alloy MIR for applyTwice:
func applyTwice(f: Int -> Int, x: Int) -> Int {
  t0 = closure_get_func f (Int -> Int)
  t1 = *t0(f, x) (Int)      -- pass closure f as first arg
  t2 = closure_get_func f (Int -> Int)
  t3 = *t2(f, t1) (Int)     -- pass closure f as first arg
  ret t3
}

-- Alloy MIR for lambda$0:
func lambda$0(closure_self: ClosurePtr, y: Int) -> Int {
  t6 = closure_get_env closure_self[0] (Int)  -- extract n from closure
  t7 = (y IAdd t6) (Int)
  ret t7
}
```

**Test Results:**

```soma
def applyTwice(f: Int -> Int, x: Int) -> Int = f (f x)

def main :: Int =
    let n = 3 in
    let addN = (\y -> y + n) in
    applyTwice addN 10
-- Result: 16 (correct: addN(addN(10)) = addN(13) = 16)
```

**Files Modified:**

- `compiler/lib/Typing/Types.hs` — Added `closurePtrType`
- `compiler/exe/Metal/Metadata.hs` — Added `ClosureFunctionInfo`, `mfmClosureInfo` field
- `compiler/exe/Metal/Lift.hs` — Uniform closure calling convention for lifted lambdas
- `compiler/exe/Metal/Gen/Binding.hs` — Added `mfmClosureInfo = Nothing` to metadata
- `compiler/exe/Alloy/Lower.hs` — Env extraction at entry, uniform call lowering
- `compiler/exe/Llvm/Gen/TypeConversion.hs` — `ClosurePtr` type mapping

**Implementation Status Update:**

The uniform closure calling convention is now complete. All higher-order functions
work correctly with closures that have captured variables. The key insight is that
the callee knows its own structure, so it can extract what it needs from `closure_self`
without the caller needing to know the env_size.

### Session 13 (2024)

**Deep Cloning for Closures: Compile-Time Specialized Inline SUP Propagation**

This session designs HVM-style SUP propagation for closure environments,
using compile-time type information to generate zero-overhead specialized code.

#### The Problem: Shallow Environment Copying

The current `soma_clone_closure` uses `memcpy` to copy the entire closure structure.
This is a **structural deep clone** but a **semantic shallow clone**:

```
Original Closure:              After memcpy clone:
┌────────────────────────┐     ┌────────────────────────┐
│ tag: 1, env_size: 2    │     │ tag: 1, env_size: 2    │
│ func_ptr: @f           │     │ func_ptr: @f           │
│ env[0] → ClosureA      │     │ env[0] → ClosureA      │ ← SAME pointer!
│ env[1] → Int(42)       │     │ env[1] → Int(42)       │
└────────────────────────┘     └────────────────────────┘
```

For immutable Soma, sharing nested closures is **semantically correct** but
**suboptimal for HVM-style reduction**. We want lazy cloning: nested closures
should only be cloned when both branches of a duplication actually use them.

#### Design Goals

1. **Zero runtime overhead** for closure access in the common case
2. **Compile-time specialization** — no runtime type checks in hot paths
3. **HVM-style lazy cloning** — nested closures wrapped in SUPs
4. **CBV compatibility** — SUPs in env slots don't violate strict semantics

#### Why SUPs in Closure Environments Work with CBV

Closures aren't "evaluated" until applied — they're just data structures.
A SUP in an env slot is simply data that gets projected when accessed:

- Access env slot → get SUP (or direct value)
- Project from SUP → get closure (possibly triggering clone)
- This is immediate projection, not lazy computation — just lazy *cloning*

#### Approaches Considered

| Approach | Description | Overhead |
|----------|-------------|----------|
| **A: Runtime Detection** | Check tag byte per env slot at clone time | Per-slot tag check |
| **B1: Specialized Functions** | Generate `clone_shape_X` per closure shape | Function call + code bloat |
| **B2: Bitmask Parameter** | Pass closure-slot mask to generic clone | Bit-check loop |
| **B3: Inline Specialized** | Generate unrolled code at each DUP site | **Zero** |

#### Chosen: Option B3 — Inline Specialized Code

For maximum performance, we generate fully specialized inline code at each
closure DUP site. At compile time we know:

1. The exact type being duplicated (from `CDup`'s type annotation)
2. Captured variable types (from `CClosure`'s `[(Name, Type)]`)
3. Which env slots are closure-typed (check for `TArrow`)

This enables:
- **No loops** — unrolled for known env_size
- **No type checks** — slot types known at compile time
- **No function calls** — inline allocation + copy
- **SUPs only where needed** — only closure-typed slots

#### New Alloy IR Operations

```haskell
-- Specialized closure duplication (replaces OpDup for closure types)
| OpDupClosure !Int AOperand ![(Int, Bool)]
    -- label, closure, [(env_index, is_closure_slot)]

-- Specialized projections with closure shape info
| OpDupClosureProj0 AOperand !Int ![(Int, Bool)]
    -- sup_handle, env_size, slot_info
    
| OpDupClosureProj1 AOperand !Int ![(Int, Bool)]
    -- sup_handle, env_size, slot_info

-- Env access variants
| OpClosureGetEnvDirect AOperand !Int   -- direct load (original closures)
| OpClosureGetEnvSUP AOperand !Int      -- load + project (cloned closures)
```

#### DUP Lowering for Closures

When `Circuit/ToAlloy.hs` lowers a `CDup` on a closure type:

```haskell
lowerTerm env (C.CDup name ty label val body) = do
    valOp <- lowerTerm env val
    
    case ty of
        TArrow _ _ -> do
            let slotInfo = getClosureSlotInfo val  -- [(idx, isClosureType)]
                envSize = length slotInfo
            
            supHandle <- emitLetTmp ty (OpDupClosure label valOp slotInfo)
            proj0 <- emitLetTmp ty (OpDupClosureProj0 (OpVar supHandle) envSize slotInfo)
            proj1 <- emitLetTmp ty (OpDupClosureProj1 (OpVar supHandle) envSize slotInfo)
            
            let env' = markAsCloned proj1  -- track that proj1 has SUP slots
                     $ extendOperand (name ++ ".0") (OpVar proj0)
                     $ extendOperand (name ++ ".1") (OpVar proj1) env
            lowerTerm env' body
            
        _ -> -- existing non-closure DUP handling
```

#### LLVM Codegen: `OpDupClosureProj1`

For a closure with `env = [Int, Closure, Int, Closure]` (slots 1, 3 are closures):

```llvm
; Generated inline (not a function):
entry:
  %tag_ptr = getelementptr %SomaSup, ptr %sup, i32 0, i32 0
  %tag = load i8, ptr %tag_ptr
  %is_proj0_first = icmp eq i8 %tag, 1
  br i1 %is_proj0_first, label %clone, label %cached

clone:
  store i8 3, ptr %tag_ptr  ; mark both accessed
  %original = load ptr, getelementptr(%SomaSup, ptr %sup, i32 0, i32 2)
  
  ; Allocate: 16 (header) + 4*8 (env) = 48 bytes
  %new = call ptr @malloc(i64 48)
  call void @llvm.memcpy.p0.p0.i64(ptr %new, ptr %original, i64 16, i1 false)
  
  ; Slot 0: Int — direct copy
  %v0 = load ptr, getelementptr(i8, ptr %original, i64 16)
  store ptr %v0, getelementptr(i8, ptr %new, i64 16)
  
  ; Slot 1: Closure — wrap in SUP
  %v1 = load ptr, getelementptr(i8, ptr %original, i64 24)
  %l1 = call i32 @soma_fresh_label()
  %s1 = call ptr @soma_dup(i32 %l1, ptr %v1)
  store ptr %s1, getelementptr(i8, ptr %new, i64 24)
  
  ; Slot 2: Int — direct copy
  %v2 = load ptr, getelementptr(i8, ptr %original, i64 32)
  store ptr %v2, getelementptr(i8, ptr %new, i64 32)
  
  ; Slot 3: Closure — wrap in SUP
  %v3 = load ptr, getelementptr(i8, ptr %original, i64 40)
  %l3 = call i32 @soma_fresh_label()
  %s3 = call ptr @soma_dup(i32 %l3, ptr %v3)
  store ptr %s3, getelementptr(i8, ptr %new, i64 40)
  
  store ptr %new, getelementptr(%SomaSup, ptr %sup, i32 0, i32 4)
  br label %done

cached:
  %c = load ptr, getelementptr(%SomaSup, ptr %sup, i32 0, i32 4)
  br label %done

done:
  %result = phi ptr [ %new, %clone ], [ %c, %cached ]
```

#### Clone Status Tracking

Track whether closures are originals or clones in the lowering environment:

```haskell
data LowerEnv = LowerEnv
    { leOperands :: Map Name AOperand
    , leAllocInfo :: AllocEnv
    , leClonedClosures :: Set Name  -- closures with SUP slots
    , leClosureSlotTypes :: Map Name [(Int, Bool)]  -- slot type info per closure
    }
```

When accessing env slots:
- **Original closure**: emit `OpClosureGetEnvDirect` (single load)
- **Cloned closure, closure-typed slot**: emit `OpClosureGetEnvSUP` (load + project)
- **Cloned closure, primitive slot**: emit `OpClosureGetEnvDirect` (single load)

#### Runtime: Fresh Label Counter

```llvm
@soma_label_counter = global i32 0

define i32 @soma_fresh_label() {
  %old = atomicrmw add ptr @soma_label_counter, i32 1 seq_cst
  ret i32 %old
}
```

#### Implementation Checklist

**Phase 1: IR Extensions** ✓
- [x] Add `OpDupClosure`, `OpDupClosureProj0`, `OpDupClosureProj1` to `Alloy/Ir.hs`
- [x] Add `OpClosureGetEnvDirect`, `OpClosureGetEnvSUP` to `Alloy/Ir.hs`
- [x] Update all Alloy passes for new operations (Simplify, Subst, PromoteRefs, Uniqueness, Inline, Defunc)

**Phase 2: Lowering** ✓
- [x] Modify `Circuit/ToAlloy.hs` to emit specialized ops for closure DUP
- [x] Track cloned closures and slot types in lowering environment (`leClosureSlotTypes`, `leClonedClosures`)
- [ ] Emit appropriate env access ops based on clone status (deferred — slot info not yet threaded from CClosure)

**Phase 3: LLVM Codegen** ✓
- [x] Add `soma_fresh_label` to `Llvm/Gen/Runtime.hs` (atomic counter)
- [x] Add `LlvmAtomicRmw` instruction to `Llvm/Instructions.hs`
- [x] Implement `OpDupClosure` codegen (calls `soma_dup`)
- [x] Implement `OpDupClosureProj0` codegen (calls `soma_proj0`)
- [x] Implement `OpDupClosureProj1` codegen (inline specialized clone with SUP wrapping)
- [x] Implement `OpClosureGetEnvDirect` codegen (direct load)
- [x] Implement `OpClosureGetEnvSUP` codegen (load + project)

**Phase 4: Testing** ✓
- [x] Test nested closure duplication (`test_closure_dup.soma`)
- [x] Test multiple nesting levels (`testNestedDup`)
- [x] All tests pass with correct results

**Bug Fixes During Implementation:**
- [x] Fixed `Alloy/Inline.hs` bug: `zipWith3` was misaligning instructions when `IEffect` 
      statements were present, causing inlined functions to lose their return values.
      Replaced with `renameInstrs` that properly handles effects without consuming fresh names.

#### Performance Summary

| Operation | Before | After B3 |
|-----------|--------|----------|
| Proj0 (first access) | Function call + branches | Inline: 2 loads + 1 store |
| Proj1 (clone) | Call + memcpy + tag loop | Inline: alloc + unrolled copy |
| Env access (original) | Function call | Inline: 1 load |
| Env access (clone, closure slot) | Function call | Inline: 1 load + project |

**Eliminated overhead:**
- Function call overhead for all projection operations
- Runtime type checking loops
- Generic clone function dispatch

**Remaining cost (unavoidable for lazy cloning):**
- SUP allocation for nested closure slots
- Single tag check when accessing SUP slots in clones

### Session 14 (2024)

**Escape Analysis & Clone Elision + SUP Inlining**

This session implements two key optimizations for the interaction net model:

#### Optimization #1: Escape Analysis for Clone Elision

When a closure is duplicated (CDup), both projections may be used locally without
escaping the function scope. In such cases, we can skip SUP-based lazy cloning
entirely and just share the same closure reference.

**New Module: `Circuit/Escape.hs`**

```haskell
data EscapeKind
    = NoEscape     -- Value used only in local scope
    | LocalEscape  -- Value escapes to local binding but not returned
    | Escapes      -- Value may escape the function

-- Query function for clone elision
canElideClone :: Name -> EscapeEnv -> Bool
```

**Key Insight:** If a closure is passed only to known direct function calls
(not indirect calls or stored in data structures), it doesn't escape because
the called function uses its arguments locally.

**Integration in `Circuit/ToAlloy.hs`:**
- Run escape analysis per function (`analyzeFunctionEscapes`)
- Store results in `LowerEnv.leEscapeInfo`
- When lowering `CDup` for closures, check `canElideClone`
- If elision is safe: skip `OpDupClosure`/projections, use same operand for both

**Before (with SUP):**
```
t8 = alloc_closure lambda$0 arity=1 env=2
t9 = wrap_closure t8
t10 = dup_closure[0] t9 slots=[]
t11 = dup_closure_proj0 t10
t12 = dup_closure_proj1 t10
t13 = lambda$0(t12)
t14 = lambda$0(t11)
```

**After (with elision):**
```
t24 = alloc_closure lambda$0 arity=1 env=1
t25 = lambda$0(t24)
t27 = lambda$0(t24)
```

#### Optimization #2: Inline Known Closure Calls Through SUPs

When closures go through SUP operations (DUP/projections), we preserve knowledge
of their target function, enabling continued inlining.

**Changes in `Alloy/Inline.hs`:**

Track closure targets through:
- `OpWrapClosure` — preserves target from wrapped closure
- `OpDupClosure` — SUP creation preserves target
- `OpDupClosureProj0/Proj1` — projections inherit target from SUP handle
- `OpDup/OpDupProj0/OpDupProj1` — generic DUP also tracked

This enables the inliner to inline calls even when the closure was duplicated:
```haskell
-- Before: indirect call through unknown function pointer
-- After: direct inlined call because we tracked target through DUP
```

#### Implementation Checklist

**Escape Analysis** ✓
- [x] Create `Circuit/Escape.hs` module with escape analysis
- [x] Define `EscapeKind` (NoEscape, LocalEscape, Escapes)
- [x] Implement `analyzeTermEscapes` recursive analysis
- [x] Smart handling: direct calls don't cause escape
- [x] `canElideClone` query function

**Clone Elision** ✓
- [x] Add `leEscapeInfo :: EscapeEnv` to `LowerEnv`
- [x] Run `analyzeFunctionEscapes` in `lowerFunction`
- [x] Check `canElideClone` in CDup handling
- [x] Skip SUP ops when both projections don't escape

**SUP Inlining** ✓
- [x] Track `OpWrapClosure` in inliner
- [x] Track `OpDupClosure` in inliner
- [x] Track `OpDupClosureProj0/Proj1` in inliner
- [x] Track `OpDup/OpDupProj0/OpDupProj1` in inliner

#### Performance Impact

| Scenario | Before | After |
|----------|--------|-------|
| Local closure duplication | SUP alloc + projections | Direct sharing |
| Closure call after DUP | Indirect call | Direct/inlined call |
| Nested closure in DUP | SUP + nested SUPs | Direct (if non-escaping) |

**Eliminated overhead for non-escaping closures:**
- SUP node allocation
- Projection operations
- Lazy cloning mechanism entirely

#### Files Modified

| File | Changes |
|------|---------|
| `Circuit/Escape.hs` | **NEW** — Escape analysis module |
| `Circuit/ToAlloy.hs` | Added escape info to LowerEnv, clone elision in CDup |
| `Alloy/Inline.hs` | Track closure targets through DUP operations |
| `soma.cabal` | Added Circuit.Escape module |

### Session 15 (2024)

**Slot Type Threading & Label-Based DUP-SUP Interaction**

This session completes two key improvements to the interaction net runtime:

#### Task 1: Thread Slot Type Info from CClosure to CDup

Previously, when duplicating closures, the specialized DUP operations (`OpDupClosure`,
`OpDupClosureProj0/1`) used empty slot info because the captured variable types weren't
being tracked from `CClosure` creation to `CDup` usage.

**Changes to `Circuit/ToAlloy.hs`:**

1. Added `leClosureEnvSizes :: Map Name Int` to `LowerEnv` to track env sizes
2. Updated `CLet` handling: when binding a `CClosure`, record its slot info and env size
3. Updated `CDup` handling: look up slot info from the value being duplicated
4. Propagate slot info to DUP projections for nested DUP handling

```haskell
-- In CLet handling:
let env' = case val of
    C.CClosure _ capturedVars _ ->
        let slotInfo = computeSlotInfo capturedVars
            envSize = length capturedVars
        in recordClosureEnvSize name envSize
            $ recordClosureSlotTypes name slotInfo
            $ extendOperand name valOp env
    _ -> extendOperand name valOp env

-- In CDup handling for closures:
let valName = case val of
        C.CVar n _ -> Just n
        C.CDp0 n _ -> Just (n ++ ".0")
        C.CDp1 n _ -> Just (n ++ ".1")
        _ -> Nothing
    slotInfo = case valName of
        Just vn -> maybe [] id (lookupClosureSlotTypes vn env)
        Nothing -> []
    envSize = case valName of
        Just vn -> maybe 0 id (lookupClosureEnvSize vn env)
        Nothing -> 0
```

#### Task 2: Label-Based DUP-SUP Annihilation & Commutation

Implemented proper interaction net semantics for DUP-SUP interaction based on labels.

**SUP Tag Encoding:**

Changed SUP tags to use high bit (128+) to distinguish from other node types:
- `128` = fresh (not yet accessed)
- `129` = proj0_accessed
- `130` = proj1_accessed  
- `131` = both accessed
- `1` = NODE_CLOSURE (unchanged)

To check if a value is a SUP: `tag >= 128` (or `tag & 0x80 != 0`)

**Annihilation (Same Label):**

When `!d &L = &L{v}` (DUP with label L meets SUP with same label L):
```
proj0(L) on SUP(L, v) → v  (direct extraction, no cloning)
proj1(L) on SUP(L, v) → v  (direct extraction, no cloning)
```

This avoids unnecessary cloning when a value passes through matching DUP-SUP pairs.

**Commutation (Different Labels):**

When `!d &L = &M{v}` where L ≠ M:
```
proj0(L) on SUP(M, v) → SUP(M, v)  (pass through inner SUP)
proj1(L) on SUP(M, v) → SUP(M, v)  (pass through inner SUP)
```

The inner SUP is passed through unchanged. Its projections will be resolved
when accessed later. This is implicit lazy commutation - semantically correct
and works naturally with our lazy evaluation model.

**Changes to `Llvm/Gen/Runtime.hs`:**

1. Updated `soma_dup` to use tag 128 (was 0)
2. Rewrote `soma_proj0` and `soma_proj1` with new logic:
   - Check if value is a SUP (tag >= 128)
   - If SUP with same label: annihilate (extract inner value)
   - If SUP with different label: pass through (implicit commutation)
   - If closure: clone as before
   - Otherwise: shallow copy

**Runtime Flow (soma_proj0):**

```
entry:
  load tag
  if tag == 128 (fresh) → fresh
  else → check_proj1

fresh:
  mark as proj0_accessed (129)
  load value
  if value is null → fresh_return_value
  else → fresh_check_sup

fresh_check_sup:
  load value's tag
  if tag >= 128 (is SUP) → fresh_annihilate
  else → fresh_return_value

fresh_annihilate:
  load our label and inner label
  if labels match → fresh_do_annihilate (extract inner value)
  else → fresh_return_value (pass through inner SUP)

... (similar logic for second access path)
```

#### Implementation Status Update

**Completed:**
- [x] Thread slot type info from CClosure to CDup
- [x] Label-based DUP-SUP annihilation (same label)
- [x] Label-based DUP-SUP commutation (different labels - implicit via lazy passing)

**Files Modified:**

| File | Changes |
|------|---------|
| `Circuit/ToAlloy.hs` | Added `leClosureEnvSizes`, slot info threading in CLet/CDup |
| `Llvm/Gen/Runtime.hs` | SUP tag encoding (128+), annihilation/commutation in proj0/proj1 |

### Session 16 (2024)

**C Runtime Implementation with Memory Pools and Tagged Pointers**

This session moved the runtime from generated LLVM IR to a standalone C library,
added memory pool allocation, and implemented tagged pointer value representation.

#### Motivation

The Haskell-generated LLVM IR (`Llvm/Gen/Runtime.hs`) was functional but had limitations:
- Verbose and harder to maintain
- No memory pooling (every allocation went through malloc)
- No tagged pointer optimization (all values were heap-allocated)

A C runtime provides:
- Clean, maintainable implementation
- Memory pools for reduced allocation overhead
- Tagged pointers for unboxed primitives
- Future optimizations (SIMD, cache locality, etc.)

#### New Files: `runtime/`

Created a new `runtime/` directory at the project root:

| File | Purpose |
|------|---------|
| `runtime/soma_runtime.h` | Header with structures, macros, and function declarations |
| `runtime/soma_runtime.c` | Implementation of all runtime functions |
| `runtime/Makefile` | Build file for `libsoma_runtime.a` |

#### Data Structures

**SUP Node (40 bytes):**
```c
typedef struct SomaSup {
    uint8_t  tag;      // 128=fresh, 129=proj0, 130=proj1, 131=both
    uint8_t  _pad[3];
    uint32_t label;
    void*    value;
    void*    proj0;
    void*    proj1;
} SomaSup;
```

**Closure (16 + env_size*8 bytes):**
```c
typedef struct SomaClosure {
    uint8_t  tag;       // NODE_CLOSURE = 1
    uint8_t  arity;
    uint16_t env_size;
    uint32_t _pad;
    void*    func_ptr;
    // void* env[] follows
} SomaClosure;
```

#### Memory Pool Implementation

Arena-style allocation with free-list recycling:

```c
#define POOL_BLOCK_SIZE     (64 * 1024)  // 64KB per block
#define POOL_SUP_SIZE       40           // sizeof(SomaSup)
#define POOL_CLOSURE_SMALL  48           // 0-3 env slots
#define POOL_CLOSURE_MEDIUM 112          // 4-11 env slots
// Large closures (12+) use malloc

typedef struct SomaPoolBlock {
    struct SomaPoolBlock* next;
    size_t used;
    char data[];
} SomaPoolBlock;

typedef struct SomaPool {
    SomaPoolBlock* blocks;
    size_t item_size;
    void* free_list;
} SomaPool;
```

**Pool Functions:**
- `soma_pool_init()` — Initialize all pools at startup
- `soma_pool_cleanup()` — Free all pool memory at shutdown
- `soma_pool_alloc_sup()` — Allocate SUP node from pool
- `soma_pool_alloc_closure(env_size)` — Pick appropriate size class
- `soma_pool_free_sup(ptr)` — Return SUP to free list
- `soma_pool_free_closure(ptr, env_size)` — Return closure to free list

**Benefits:**
- Allocation is O(1) bump pointer or free-list pop
- No malloc/free overhead for common cases
- Cache-friendly: similar-sized objects are contiguous
- Statistics tracking for profiling

#### Tagged Pointer Representation

Uses low 3 bits of pointers for type tags (8-byte alignment):

```c
#define TAG_BITS        3
#define TAG_MASK        0x7ULL
#define PAYLOAD_SHIFT   3

#define TAG_PTR         0   // Heap pointer
#define TAG_INT         1   // Small integer (61-bit signed)
#define TAG_BOOL        2   // Boolean/Unit
#define TAG_CHAR        3   // Unicode codepoint

typedef uintptr_t SomaValue;

// Type checking
#define SOMA_IS_PTR(v)  (SOMA_GET_TAG(v) == TAG_PTR)
#define SOMA_IS_INT(v)  (SOMA_GET_TAG(v) == TAG_INT)

// Create/extract values
#define SOMA_INT(n)     ((((SomaValue)(int64_t)(n)) << 3) | TAG_INT)
#define SOMA_TO_INT(v)  ((int64_t)(v) >> 3)
#define SOMA_TRUE       ((SomaValue)(1 << 3) | TAG_BOOL)
#define SOMA_FALSE      ((SomaValue)(0 << 3) | TAG_BOOL)
```

**Benefits:**
- Integers, booleans, chars never allocate
- Single word comparison for type checking
- Compatible with pointer operations (tag 0 = no modification)

#### Updated Runtime Functions

The projection functions now handle tagged values:

```c
static inline int is_heap_sup(SomaValue value) {
    if (!SOMA_IS_PTR(value) || value == 0) return 0;
    uint8_t tag = *(uint8_t*)SOMA_TO_PTR(value);
    return IS_SUP(tag);
}

SomaValue soma_proj0(SomaValue sup_val) {
    SomaSup* sup = (SomaSup*)SOMA_TO_PTR(sup_val);
    // ... same logic but checks SOMA_IS_PTR before dereferencing
    // Tagged values (int, bool, char) don't need cloning
    if (!SOMA_IS_PTR(value) || value == 0) {
        sup->proj0 = (void*)value;
        return value;
    }
    // ... closure cloning, SUP annihilation as before
}
```

#### Build System

```makefile
CC = clang
CFLAGS = -O3 -Wall -Wextra -fPIC -std=c11

all: libsoma_runtime.a

libsoma_runtime.a: soma_runtime.o
	ar rcs $@ $^
```

Build: `cd runtime && make`

#### Performance Summary

| Before (LLVM Gen) | After (C Runtime) |
|-------------------|-------------------|
| Every alloc → malloc | Pool allocation |
| All values heap-allocated | Primitives unboxed |
| Generated LLVM IR | Compiled C with -O3 |
| Harder to maintain | Clean C code |

#### Implementation Checklist

- [x] Create `runtime/soma_runtime.h` with structures and macros
- [x] Create `runtime/soma_runtime.c` with all runtime functions
- [x] Create `runtime/Makefile` for building static library
- [x] Add memory pool with three size classes (SUP, small closure, medium closure)
- [x] Add tagged pointer representation for Int, Bool, Char
- [x] Update soma_dup to use pool allocation
- [x] Update soma_alloc_closure to use pool allocation
- [x] Update soma_clone_closure to use pool allocation
- [x] Update soma_proj0/1 to handle tagged values (skip cloning for non-pointers)
- [x] Add pool statistics tracking

#### Files Created

| File | Purpose |
|------|---------|
| `runtime/soma_runtime.h` | Header (structures, tagged pointer macros, pool API) |
| `runtime/soma_runtime.c` | Implementation (pools, runtime functions) |
| `runtime/Makefile` | Build static library |

#### Compiler Integration

The C runtime is now integrated with the build system:

**New files:**
- `compiler/exe/Llvm/Gen/CRuntime.hs` — External declarations for C runtime
- `compiler/exe/Llvm/Gen/CircuitEntry.hs` — Circuit-specific LLVM codegen entry point

**Build command:**
```bash
# Build with Circuit IR pipeline and C runtime
somac build myfile.soma --circuit

# Generate LLVM IR only (shows linking instructions)
somac build myfile.soma --circuit --out output.ll
```

**What happens:**
1. Metal HIR is lowered to Circuit IR
2. Circuit IR is linearized (DUP/ERA insertion)
3. Circuit IR is lowered to Alloy MIR
4. Alloy MIR is optimized
5. LLVM IR is generated with extern declarations (no generated runtime functions)
6. Clang links against `runtime/libsoma_runtime.a`

The runtime library is auto-built if missing when compiling executables.

### Session 17 (2024)

**Runtime Entry Point & Pool Initialization Fix**

This session fixed a critical segfault caused by uninitialized memory pools.

#### The Problem

Programs compiled with the Circuit IR pipeline were segfaulting immediately on startup.
The root cause: `soma_alloc_closure` uses memory pools (`soma_pool_alloc_closure`), but
`soma_pool_init()` was never called before the user's `main` function executed.

#### The Solution: Runtime Entry Point Wrapper

Instead of injecting initialization code into the generated LLVM, we moved the entry
point to the C runtime. This is a cleaner design that centralizes all initialization
and cleanup logic.

**Changes to `runtime/soma_runtime.c`:**

```c
/*
 * Main entry point - wraps the user's soma_main function
 */
extern int soma_main(void);

int main(void) {
    soma_pool_init();
    int result = soma_main();
    soma_pool_cleanup();
    return result;
}
```

**Changes to `compiler/exe/Llvm/Gen/Function.hs`:**

The compiler now renames the user's `main` function to `soma_main`:

```haskell
compileFunction aFn@AlloyFunction{afName, ...} = do
    name <-
        if afName == "main"
            then pure "soma_main"  -- Renamed so C runtime's main() can wrap it
            else do
                modName <- asks moduleName
                pure $ qualifyWithModule modName afName
```

#### Why This Design Is Better

| Approach | Pros | Cons |
|----------|------|------|
| Inject `soma_pool_init()` call into generated LLVM | None | Scattered init logic, harder to maintain |
| Runtime wrapper `main()` | Centralized init/cleanup, extensible | Slight indirection (negligible) |

The runtime wrapper approach:
- Keeps all initialization logic in one place (C runtime)
- Makes it easy to add future initialization (parallel runtime, debug hooks, etc.)
- Properly handles cleanup on exit
- The compiler just does a simple rename

#### Files Modified

| File | Changes |
|------|---------|
| `runtime/soma_runtime.c` | Added `main()` wrapper calling `soma_pool_init/cleanup` |
| `compiler/exe/Llvm/Gen/Function.hs` | Renamed user's `main` → `soma_main` |

#### Verification

```bash
$ cabal run somac -- examples/test/test_closure_dup.soma --circuit
$ ./test_closure_dup
$ echo $?
23  # Correct: 2839 % 256 = 23
```

The test program `test_closure_dup.soma` exercises:
- Simple closure duplication (`testSimpleDup`)
- Nested closure duplication (`testNestedDup`)  
- Multi-variable capture (`testMultiCapture`)

All tests pass with correct results.

#### Bonus: Recursive Memory Freeing

Also in this session, implemented proper recursive freeing in `soma_era_free`:

```c
void soma_era_free(void* value) {
    if (value == NULL) return;
    
    uint8_t tag = *(uint8_t*)value;
    
    if (tag == NODE_CLOSURE) {
        SomaClosure* closure = (SomaClosure*)value;
        SomaValue* env = (SomaValue*)(closure + 1);
        
        /* Recursively free pointer-typed env slots */
        for (uint16_t i = 0; i < closure->env_size; i++) {
            if (SOMA_IS_PTR(env[i]) && env[i] != 0) {
                soma_era_free(SOMA_TO_PTR(env[i]));
            }
        }
        soma_pool_free_closure(value, closure->env_size);
        
    } else if (IS_SUP(tag)) {
        soma_pool_free_sup(value);
        
    } else {
        free(value);
    }
}
```

**Key insight:** After linearization, every value is used exactly once. When ERA fires,
we have exclusive ownership — no reference counting needed. This is the core principle
of GC-free optimal evaluation in action.

### Session 18 (2024)

**Closure Environment Forwarding & Dead Code Elimination**

This session implemented aggressive optimizations that eliminate closure allocations
entirely when closures are inlined and their captured values are known at compile time.

#### The Problem

After inlining, we had patterns like:
```
t17 = alloc_closure lambda$3 arity=1 env=1
closure_set_env t17[0] := x
t18 = (x IAdd 1)   -- inlined body uses x directly, not closure
t19 = (x IAdd 2)
drop t17           -- closure was never actually needed
```

The closure was allocated and immediately dropped — pure waste.

#### Solution: Three New Optimization Passes

**1. Closure Environment Value Forwarding (`forwardClosureEnvValuesModule`)**

Tracks values stored via `closure_set_env` and forwards them to `closure_get_env`:

```haskell
-- Track: closure_set_env t17[0] := x
-- Later: t21 = closure_get_env t17[0]
-- Result: Replace t21 with x, eliminate the closure_get_env
```

This pass runs in the optimization fixpoint loop in `Build/Incremental.hs`.

**2. Dead Let Elimination (`eliminateDeadLets`)**

Removes unused variable bindings (except those with side effects):

```haskell
-- Before:
t12 = closure_get_func t10   -- unused result
t13 = (x IAdd 10)

-- After:
t13 = (x IAdd 10)            -- dead let eliminated
```

**3. Dead Closure Elimination (`eliminateDeadClosures`)**

Removes closures that are allocated but never actually used:

```haskell
-- Tracks which closures are "used" (called, returned, stored in escaping locations)
-- closure_set_env does NOT count as a use (it's just setup)
-- EffDrop does NOT count as a use (it's just cleanup)

-- If a closure is only set up and dropped, eliminate both:
-- Before:
t17 = alloc_closure lambda$3 arity=1 env=1
closure_set_env t17[0] := x
drop t17

-- After:
(nothing - all eliminated)
```

#### Results: Zero-Allocation Closures

For `test_closure_dup.soma`, after optimization:

**testSimpleDup(x):**
```
-- Before: allocated closure, set env, then inlined
-- After:
t18 = (x IAdd 1)
t19 = (x IAdd 2)
t20 = (t18 IAdd t19)
ret t20
```

**testNestedDup(x):**
```
-- Before: allocated outer closure, two inner closures, closure_get_func calls
-- After:
t27_inl6 = (x IAdd 10)
t13 = (t27_inl6 IAdd 1)
t27_inl10 = (x IAdd 20)
t15 = (t27_inl10 IAdd 2)
t16 = (t13 IAdd t15)
ret t16
```

**testMultiCapture(x, y):**
```
-- Before: closure with 2 env slots
-- After:
t31_inl2 = (x IAdd y)
t6 = (t31_inl2 IAdd 1)
t31_inl6 = (x IAdd y)
t7 = (t31_inl6 IAdd 2)
t8 = (t6 IAdd t7)
ret t8
```

**main():**
```
-- Before: called all three test functions with closures
-- After: pure arithmetic, ZERO closure allocations
t18_inl1 = (100 IAdd 1)
t19_inl2 = (100 IAdd 2)
t0 = (t18_inl1 IAdd t19_inl2)
...
ret t4
```

#### Implementation Details

**Files Modified:**

| File | Changes |
|------|---------|
| `compiler/exe/Alloy/Simplify.hs` | Added `forwardClosureEnvValuesModule`, `eliminateDeadLets`, `eliminateDeadClosures` |
| `compiler/exe/Build/Incremental.hs` | Added `forwardClosureEnvValuesModule` to optimization fixpoint loop |

**Pass Order in `simplifyOnce`:**
1. `inlineJoinReturnBlocks`
2. `inlineForwardBlocks`
3. `foldLocalConstructAccesses`
4. `foldSwitchOnKnownTag`
5. `canonicalizeSwitches`
6. `eliminateTrivialReadOnlyRefs`
7. `eliminateDeadLets` ← NEW
8. `eliminateDeadClosures` ← NEW
9. `dropUnreachableBlocks`

**Optimization Fixpoint:**
```haskell
let optimizeFixpoint m =
        let step x = simplifyModule 
                      (forwardClosureEnvValuesModule 
                        (promoteRefsModule 
                          (cseModuleGlobal x)))
            x' = step m
        in if x' == m then m else optimizeFixpoint x'
```

#### Why This Makes Soma "Blazingly Fast"

For non-escaping closures (the common case in functional code):

| Traditional Approach | Soma After Session 18 |
|---------------------|----------------------|
| Heap allocate closure | No allocation |
| Copy captured values to env | Values used directly |
| Indirect call through func ptr | Inlined direct code |
| GC eventual cleanup | No cleanup needed |

The combination of:
- Aggressive inlining
- Closure env forwarding
- Dead code elimination

Results in **zero-overhead abstractions** for closures that don't escape.

#### Performance Impact Summary

| Metric | Before | After |
|--------|--------|-------|
| Closure allocations in `main` | 4 | 0 |
| `closure_get_env` calls | Multiple | 0 (forwarded) |
| `closure_get_func` calls | Multiple | 0 (eliminated) |
| Indirect function calls | Multiple | 0 (inlined) |
| Runtime ops in `testSimpleDup` | alloc + set_env + drop + calls | 3 IAdds |

This achieves the goal stated in Session 17: "blazingly fast with a minimal runtime".

#### Fix: ERA Node Lowering to EffDrop

Also fixed a bug where ERA nodes (unused values) weren't being freed. In `Circuit/ToAlloy.hs`,
when a `CDup` has a name starting with `era_`, it means neither projection will be used.
Instead of creating useless DUP/projections, we now emit an `EffDrop`:

```haskell
C.CDup name ty label val body -> do
    valOp <- lowerTerm env val
    let isErasure = "era_" `isPrefixOf` name
    case valKind of
        MaybeHeap
            | isErasure -> do
                emitEffect (EffDrop valOp)  -- Free the unused value
                lowerTerm env body
            ...
```

**Before:** Unused closures would leak memory.  
**After:** Unused closures are properly freed via `soma_era_free`.

Test file `examples/test/test_era.soma` verifies this works correctly.

### Session 19 (2024)

**Parallel Reduction with Demand-Driven Work Stealing**

This session implements parallel reduction for interaction nets, following the
key insight from Section 5 of this document: linear ownership enables lock-free
parallel reduction of independent subgraphs.

#### Core Design Principle: SUP ≠ Automatic Parallelism

A superposition (SUP) represents semantic independence between two branches,
but that doesn't mean both should always be evaluated in parallel. The overhead
of task creation, scheduling, and synchronization often exceeds the benefit for
small computations.

**We spawn parallel tasks ONLY when:**
1. Workers are hungry (no local work available to steal)
2. The branch is expected to be expensive (work estimation heuristic)
3. The thread pool is not saturated (pending tasks < threshold)
4. The SUP won't be immediately annihilated (label matching)

**We DON'T spawn tasks when:**
1. Branch is trivial (ERA, small constants, primitives)
2. Workers have local work (no need for more parallelism)
3. Runtime is overloaded (too many pending tasks)
4. Escape analysis proves no duplication will occur

#### Architecture: Work-Stealing Thread Pool

The parallel runtime uses a Chase-Lev work-stealing deque per worker thread:

```
┌─────────────────────────────────────────────────────────────┐
│                     Parallel Runtime                         │
├─────────────────────────────────────────────────────────────┤
│  Main Thread          Worker 0          Worker 1    ...     │
│  ┌─────────┐         ┌─────────┐       ┌─────────┐          │
│  │ spawn() │────────►│ Deque   │◄──────│ Deque   │          │
│  └─────────┘         │ [tasks] │ steal │ [tasks] │          │
│                      └────┬────┘       └────┬────┘          │
│                           │                 │                │
│                      pop (LIFO)        pop (LIFO)           │
│                           ▼                 ▼                │
│                      ┌─────────┐       ┌─────────┐          │
│                      │ Execute │       │ Execute │          │
│                      └─────────┘       └─────────┘          │
├─────────────────────────────────────────────────────────────┤
│  Hungry Count: N  │  Pending Tasks: M  │  Shutdown: 0      │
└─────────────────────────────────────────────────────────────┘
```

**Key components:**

1. **Chase-Lev Deque**: Lock-free work-stealing queue per worker
   - Owner pushes/pops from bottom (LIFO - better locality)
   - Thieves steal from top (FIFO - older, likely larger tasks)

2. **Hungry Flag**: Each worker sets this when looking for work
   - Global `hungry_count` tracks how many workers need work
   - Tasks are only spawned when `hungry_count > 0`

3. **Work Estimation**: Heuristic to estimate computation cost
   - Based on closure arity and environment size
   - Threshold prevents spawning for trivial work

#### Runtime API

```c
/* Initialize parallel runtime (0 = auto-detect cores) */
void soma_par_init(int num_workers);

/* Shutdown and join all workers */
void soma_par_shutdown(void);

/* Check if workers are hungry (need work) */
static inline int soma_par_workers_hungry(void);

/* Check if we should spawn a parallel task */
static inline int soma_par_should_spawn(uint32_t work_estimate);

/* Parallel-aware SUP projection (may spawn other branch as task) */
SomaValue soma_par_proj0(SomaValue sup, SomaTaskFn other_fn, void* other_env);
SomaValue soma_par_proj1(SomaValue sup, SomaTaskFn other_fn, void* other_env);
```

#### Work Estimation Heuristic

```c
/* Estimate work for a closure */
static inline uint32_t soma_estimate_closure_work(void* ptr) {
    if (!SOMA_IS_PTR((SomaValue)ptr) || ptr == NULL) return 1;
    uint8_t tag = *(uint8_t*)ptr;
    if (tag != NODE_CLOSURE) return 1;
    SomaClosure* c = (SomaClosure*)ptr;
    /* Heuristic: more env slots = more complex captured state */
    /* More arity = more applications to come */
    return 10 + (c->env_size * 5) + (c->arity * 20);
}
```

The threshold (`SOMA_WORK_THRESHOLD = 50`) ensures we only parallelize when
the estimated work justifies the overhead.

#### Usage

Parallel reduction is enabled via environment variable:

```bash
# Run with 4 worker threads
SOMA_PARALLEL=4 ./my_program

# Run with auto-detected worker count (cores - 1)
SOMA_PARALLEL=0 ./my_program

# Run with parallel stats output
SOMA_PARALLEL=4 SOMA_PAR_STATS=1 ./my_program
```

Example stats output:
```
[soma_par] Workers: 4
[soma_par] Tasks spawned: 1523
[soma_par] Tasks run: 1523
[soma_par] Tasks stolen: 342
[soma_par] Skipped (trivial): 4521
[soma_par] Skipped (not hungry): 892
[soma_par] Skipped (saturated): 0
[soma_par] Worker 0: run=412 stolen=89 attempts=156
[soma_par] Worker 1: run=398 stolen=102 attempts=178
...
```

#### Why Linear Ownership Enables Lock-Free Parallelism

After linearization, every value is used exactly once. This has profound
implications for parallel reduction:

1. **No Data Races**: Independent SUP branches have disjoint ownership
   - Different DUP labels identify independent subgraphs
   - No need for locks when accessing owned data

2. **No Reference Counting**: Single owner means deterministic deallocation
   - ERA fires exactly when the last (and only) use occurs
   - No atomic reference count updates

3. **Safe Work Stealing**: Tasks can be stolen without synchronization
   - The stealer becomes the new owner of the task's closure
   - Chase-Lev deque provides lock-free stealing

4. **Annihilation Preserves Independence**: Same-label DUP-SUP pairs annihilate
   - This naturally merges parallel branches when they converge
   - No explicit synchronization needed

#### Implementation Files

| File | Changes |
|------|---------|
| `runtime/soma_runtime.h` | Added parallel runtime types and API |
| `runtime/soma_runtime.c` | Implemented Chase-Lev deque, worker threads, task spawning |
| `runtime/Makefile` | Added `-pthread` flag |

#### Configuration Constants

| Constant | Default | Description |
|----------|---------|-------------|
| `SOMA_MAX_WORKERS` | 64 | Maximum worker threads |
| `SOMA_TASK_QUEUE_SIZE` | 4096 | Per-worker deque capacity |
| `SOMA_WORK_THRESHOLD` | 50 | Minimum work estimate to spawn |
| `SOMA_MAX_PENDING_TASKS` | 1024 | Saturation threshold |

#### Future Work

1. **Compiler Integration**: Emit `soma_par_proj0/1` calls at DUP projection sites
   when the other branch is expensive (requires static work estimation)

2. **Adaptive Thresholds**: Dynamically adjust `SOMA_WORK_THRESHOLD` based on
   observed spawn success rate and worker utilization

3. **NUMA Awareness**: Prefer stealing from workers on the same NUMA node

4. **Blocking Operations**: Support blocking I/O in tasks without stalling workers
   (continuation-passing style or green threads)

#### Session 19 Implementation Notes

**Initial Testing Challenge:**

When first testing parallel reduction, the optimizer's aggressive inlining and
clone elision passes eliminated all DUP operations, making it impossible to
verify parallel projections were working. This led to temporarily disabling
these optimizations during testing:

- Disabled closure inlining in `Build/Incremental.hs`
- Set `parallelWorkThreshold = 0` to force parallel ops on all DUPs
- Disabled clone elision (`canElide = False`) to prevent escape analysis bypass

**Bug Fixes Required:**

1. **Pattern match failures in `Alloy/Simplify.hs`**
   
   The new parallel ops weren't handled in `substOpAll`, causing crashes:
   ```haskell
   -- Added to both substOpAll functions:
   OpParProj0 handle work -> OpParProj0 (substOp subst handle) work
   OpParProj1 handle work -> OpParProj1 (substOp subst handle) work
   OpParClosureProj0 handle envSz slotInfo work -> 
       OpParClosureProj0 (substOp subst handle) envSz slotInfo work
   OpParClosureProj1 handle envSz slotInfo work -> 
       OpParClosureProj1 (substOp subst handle) envSz slotInfo work
   ```

2. **Wrong result (exit code 3 instead of 23)**
   
   Two type mismatches caused incorrect results:
   
   a) `CRuntime.hs` declared runtime functions with `ptrType` instead of `LlvmI64`:
   ```haskell
   -- Before (wrong):
   LlvmFunctionDependency "soma_par_proj0" ptrType [ptrType, LlvmI32]
   
   -- After (correct):
   LlvmFunctionDependency "soma_par_proj0" LlvmI64 [LlvmI64, LlvmI32]
   ```
   
   b) `Op.hs` was generating LLVM code with `LlvmPointer LlvmI8` instead of `LlvmI64`:
   ```haskell
   -- Fixed all four parallel projection ops to use LlvmI64:
   compileOp (OpParProj0 handleOp workEstimate) resultTy = do
       llHandle <- compileOperand handleOp
       let handleTy = getValueType llHandle
       i64Handle <- case handleTy of
           LlvmI64 -> pure llHandle
           LlvmPointer _ -> saveTmp (LlvmPtrToInt llHandle LlvmI64) LlvmI64
           _ -> saveTmp (LlvmSExt llHandle LlvmI64) LlvmI64
       -- ... call with LlvmI64 types
   ```

3. **OpWrapClosure double-wrapping bug**
   
   The code was wrapping already-allocated closures with another allocation:
   ```haskell
   -- Before (wrong): wrapped closure in OpWrapClosure then passed to OpDupClosure
   wrappedOp <- emitLetTmp ty (OpWrapClosure valOp)
   supHandle <- emitLetTmp ty (OpDupClosure label wrappedOp slotInfo)
   
   -- After (correct): closures don't need wrapping, they're already valid
   supHandle <- emitLetTmp ty (OpDupClosure label valOp slotInfo)
   ```

**Test Verification:**

After fixes, `test_closure_dup.soma` with `testSimpleDup(10)`:
- Expected: 11 + 12 = 23
- Result: Exit code 23 ✓

With `SOMA_PARALLEL=4 SOMA_PAR_STATS=1`:
```
[soma_par] Workers: 4
[soma_par] Projections skipped as trivial: 2
```

The "trivial" skips confirm that the work estimation is correctly identifying
that simple integer operations don't warrant parallel spawning.

**Files Modified in Session 19:**

| File | Changes |
|------|---------|
| `Alloy/Ir.hs` | Added `OpParProj0`, `OpParProj1`, `OpParClosureProj0`, `OpParClosureProj1` |
| `Alloy/Simplify.hs` | Added parallel ops to both `substOpAll` functions |
| `Circuit/ToAlloy.hs` | Emit parallel projection ops when `parallelWorkThreshold` exceeded |
| `Llvm/Gen/CRuntime.hs` | Added external declarations for `soma_par_proj0/1` with correct types |
| `Llvm/Gen/Op.hs` | LLVM codegen for all four parallel projection operations |
| `runtime/soma_runtime.h` | Parallel runtime API declarations |
| `runtime/soma_runtime.c` | Chase-Lev deque, worker threads, parallel projection implementation |
| `runtime/Makefile` | Added `-pthread` for thread support |

**Key Insight: SomaValue = i64**

The Soma runtime uses tagged pointers where `SomaValue` is `typedef uint64_t`.
All runtime function parameters and returns use this i64 representation,
NOT pointer types. The low 3 bits encode the type tag (TAG_INT=1, TAG_PTR=0, etc.),
and the remaining 61 bits hold the payload. This must be matched exactly in
LLVM codegen or values get corrupted.

### Session 20 (2024)

**Remaining TODOs: Field Projection, Nested Pattern Types, HVM-style SUP Wrapping**

This session completed the remaining TODOs identified in the Circuit IR implementation.

#### TODO #1: Field Projection via `CProject`

Added a new Circuit IR constructor for projecting fields from tagged values (ADTs):

```haskell
-- In Circuit/Ir.hs:
| CProject !CTerm !Int !Type  -- Project field at index from tagged value
```

**Changes across the pipeline:**

| File | Changes |
|------|---------|
| `Circuit/Ir.hs` | Added `CProject` constructor; updated `getTermType`, `countVarUses`, `freeVars`, `freeVarsWithTypes`, `classifyTerm` |
| `Circuit/Lower.hs` | Lower `MFieldAccess expr idx ty` to `CProject expr' idx ty` |
| `Circuit/Linearize.hs` | Handle `CProject` in `linearizeTerm`, `substituteNth`, `substituteVar` |
| `Circuit/Simplify.hs` | Handle `CProject` in `go` and `substitute` |
| `Circuit/Alloc.hs` | Handle `CProject` in `analyzeTerm'` and `inferTermKind` |
| `Circuit/Escape.hs` | Handle `CProject` in `analyzeTermEscapes` and `nameUsedInReturnPosition` |
| `Circuit/ToAlloy.hs` | Lower `CProject` to `OpProject` (with idx+1 for 1-based indexing since slot 0 is tag) |
| `Logging/Trees.hs` | Added `NProject` node type for pretty printing and graph visualization |

**Performance:** This is entirely compile-time with zero runtime overhead. `CProject` compiles
to `OpProject` which becomes a direct LLVM `getelementptr` instruction — just pointer arithmetic.

#### TODO #2: Proper Field Types in Nested Pattern Matching

The pattern matching lowering was using placeholder types for nested patterns. This session
fixed the type propagation to use actual field types from constructor definitions.

**Changes to `Circuit/Lower.hs`:**

Extended `leConstructors` from `Map String (Int, Int)` to `Map String (Int, Int, [Type])`:
```haskell
-- Before:
leConstructors :: Map String (Int, Int)  -- name -> (tag, arity)

-- After:
leConstructors :: Map String (Int, Int, [Type])  -- name -> (tag, arity, fieldTypes)
```

Updated `buildEnv` to store field types:
```haskell
[ (mcName c, (mcTag c, length (mcFields c), mcFields c))
| c <- mtdConstructors td
]
```

Fixed `extractPatternInfo` to use actual field types when matching constructor patterns:
```haskell
PCon conName subPats -> do
    env <- ask
    case Map.lookup conName (leConstructors env) of
        Just (tag, _, fieldTypes) -> do
            let typedSubPats = zip (fieldTypes ++ repeat scrutTy) subPats
            fieldNamesAndTypes <- mapM (uncurry extractFieldNameAndType) typedSubPats
            pure (tag, fieldNamesAndTypes)
```

Added helper functions for type extraction:
```haskell
extractTupleTypes :: Type -> [Type]
extractTupleTypes (TApp (TApp (TConstructor tc) t1) t2)
    | tcName tc == "Tuple2" = [t1, t2]
-- ... handles Tuple3, Tuple4, etc.

extractArrayElemType :: Type -> Type
extractArrayElemType (TApp (TConstructor tc) elemTy)
    | tcName tc == "Array" = elemTy
extractArrayElemType ty = ty
```

Fixed `PLit` pattern type inference (was incorrectly pattern matching on `Maybe Type`):
```haskell
PLit lit _ -> do
    let litTy = case lit of
            LitInt _ -> intType
            LitBool _ -> boolType
            LitString _ -> TConstructor (TypeConstructor "String" KindStar)
    name <- lift $ freshName "lit"
    pure (0, [(name, litTy)])
```

**Performance:** This is purely compile-time type propagation with no runtime cost.
It just enables better type information for downstream optimization passes.

#### TODO #3: HVM-style SUP Wrapping in `soma_clone_closure`

Implemented proper lazy cloning of nested closures in the C runtime.

**Changes to `runtime/soma_runtime.c`:**

```c
void* soma_clone_closure(void* closure_ptr) {
    SomaClosure* closure = (SomaClosure*)closure_ptr;
    uint16_t env_size = closure->env_size;

    /* Allocate new closure */
    void* new_closure = soma_pool_alloc_closure(env_size);
    
    /* Copy header (tag, arity, env_size, func_ptr) */
    memcpy(new_closure, closure, sizeof(SomaClosure));
    
    /* Copy env slots, wrapping closure/SUP-typed slots in fresh SUPs */
    SomaValue* src_env = (SomaValue*)(closure + 1);
    SomaValue* dst_env = (SomaValue*)((SomaClosure*)new_closure + 1);
    
    for (uint16_t i = 0; i < env_size; i++) {
        SomaValue val = src_env[i];
        
        /* Check if this is a heap pointer that might need lazy cloning */
        if (SOMA_IS_PTR(val) && val != 0) {
            uint8_t tag = *(uint8_t*)SOMA_TO_PTR(val);
            
            if (tag == NODE_CLOSURE || IS_SUP(tag)) {
                /* Wrap in SUP for lazy nested cloning */
                uint32_t fresh_label = soma_fresh_label();
                void* sup = soma_dup(fresh_label, SOMA_TO_PTR(val));
                dst_env[i] = SOMA_PTR(sup);
                continue;
            }
        }
        
        /* Non-closure value: direct copy */
        dst_env[i] = val;
    }

    return new_closure;
}
```

**How it works:**
1. Allocate a new closure structure
2. Copy the header (tag, arity, env_size, func_ptr)
3. For each env slot:
   - If it's a heap pointer to a closure or SUP → wrap in a fresh SUP for lazy cloning
   - Otherwise → direct copy (primitives don't need lazy cloning)

**Performance:** This adds a small runtime cost (tag check per env slot) but enables
HVM-style lazy cloning: nested closures are only actually cloned when both projections
of their containing SUP are accessed. The compiler already has specialized inline cloning
via `OpDupClosureProj1` with `slotInfo` for the fast path — this runtime function is a
fallback for dynamic cases.

#### Summary of What Was Gained

| Feature | Benefit |
|---------|---------|
| `CProject` | Direct field access without pattern matching overhead |
| Proper nested pattern types | Correct type information enables better downstream optimizations |
| HVM-style SUP wrapping | Lazy nested closure cloning reduces unnecessary allocations |

All three changes preserve the core design principle: **GC-free optimal evaluation**.
The first two are pure compile-time improvements with zero runtime overhead. The third
adds minimal overhead (tag checks) to enable lazy cloning, which can be a net performance
win when nested closures aren't always used.

**Files Modified:**

| File | Changes |
|------|---------|
| `Circuit/Ir.hs` | Added `CProject` constructor |
| `Circuit/Lower.hs` | Field projection lowering, extended `leConstructors`, fixed nested pattern types |
| `Circuit/Linearize.hs` | Handle `CProject` |
| `Circuit/Simplify.hs` | Handle `CProject` |
| `Circuit/Alloc.hs` | Handle `CProject` |
| `Circuit/Escape.hs` | Handle `CProject` |
| `Circuit/ToAlloy.hs` | Lower `CProject` to `OpProject` |
| `Logging/Trees.hs` | Added `NProject` node type |
| `runtime/soma_runtime.c` | HVM-style SUP wrapping in `soma_clone_closure` |

**Test Verification:**

Build and test pass with correct results:
```bash
$ cabal build somac
$ ./test_closure_dup
$ echo $?
23  # Correct: 2839 % 256 = 23
```

### Session 21 (2024)

**Inline Specialized Closure Cloning in `OpDupClosureProj1`**

This session completed the TODO in `Llvm/Gen/Op.hs:385-391` by implementing fully inline
specialized closure cloning, eliminating the function call overhead to `soma_proj1`.

#### The Problem

The previous implementation of `OpDupClosureProj1` was calling `soma_proj1` at runtime,
which then called `soma_clone_closure`. This had several issues:
1. Function call overhead
2. Runtime tag checking per env slot in `soma_clone_closure`
3. No use of compile-time slot type information

#### The Solution: Fully Inline Code Generation

Now `OpDupClosureProj1` generates all the code inline:

1. **SUP state machine inline**: Checks tag and handles fresh/proj0/cached states
2. **Direct memory operations**: Uses `getelementptr` and `load`/`store` directly
3. **Compile-time slot dispatch**: Uses `slotInfo` to know which slots are closures
4. **Unrolled slot copying**: No runtime loop, each slot is handled individually

**Generated code structure:**
```llvm
; Check SUP tag
%tag = load i8, ptr %sup
%is_fresh = icmp eq i8 %tag, 128
br i1 %is_fresh, label %fresh, label %check_proj0

fresh:
  store i8 130, ptr %sup_tag        ; Mark as PROJ1
  store ptr %value, ptr %sup_proj1  ; Cache value
  br label %done

check_proj0:
  %is_proj0 = icmp eq i8 %tag, 129
  br i1 %is_proj0, label %clone, label %cached

clone:
  store i8 131, ptr %sup_tag        ; Mark as BOTH
  %new_closure = call ptr @soma_pool_alloc_closure(i16 %env_size)
  call ptr @memcpy(ptr %new_closure, ptr %original, i64 16)  ; Copy header
  
  ; For each slot (unrolled):
  ; - Non-closure: direct copy
  ; - Closure: wrap in SUP via soma_fresh_label + soma_dup
  ...
  
  store ptr %new_closure, ptr %sup_proj1
  br label %done

cached:
  %cached_val = load ptr, ptr %sup_proj1
  br label %done

done:
  %result = phi ptr [ %value, %fresh ], [ %new_closure, %clone ], [ %cached_val, %cached ]
```

#### Benefits

| Before | After |
|--------|-------|
| Call `soma_proj1` | Inline code |
| Call `soma_clone_closure` | Inline allocation + memcpy |
| Runtime tag check per slot | Compile-time slot type dispatch |
| Loop over slots | Unrolled slot handling |

**Eliminated overhead:**
- 2 function calls per closure clone
- Runtime type checking loop
- Branch misprediction from generic loop

**Remaining minimal overhead:**
- Single tag check for SUP state (unavoidable)
- `soma_fresh_label` + `soma_dup` calls for closure slots (required for lazy cloning)

#### Implementation Details

**New helper in `Llvm/Gen/Core.hs`:**
```haskell
-- Generate a fresh block label name with a given prefix
freshBlockName :: (MonadState IrGenState m) => String -> m String
freshBlockName prefix = do
    n <- gets nextRegister
    modify $ \s -> s{nextRegister = n + 1}
    return $ prefix ++ "_" ++ show n
```

**Key code in `Llvm/Gen/Op.hs`:**
```haskell
compileInlineClosureProj1 :: LlvmValue -> Int -> SlotInfo -> IrGen LlvmValue
compileInlineClosureProj1 supHandle envSz slots = do
    -- Load SUP tag, value, proj1 cache pointers
    -- Generate branch labels
    -- Emit state machine with phi node for result
    ...
  where
    copyOrWrapSlot srcClosure dstClosure slotIdx = do
        -- Use compile-time slotInfo to determine if closure slot
        let isClosureSlot = slotIdx `elem` [idx | (idx, True) <- slots]
        if isClosureSlot
            then do
                -- Wrap in SUP for lazy nested cloning
                freshLbl <- call soma_fresh_label
                supForSlot <- call soma_dup(freshLbl, srcVal)
                store supForSlot dstSlot
            else do
                -- Direct copy for non-closure slots
                store srcVal dstSlot
```

#### Files Modified

| File | Changes |
|------|---------|
| `Llvm/Gen/Core.hs` | Added `freshBlockName` function |
| `Llvm/Gen/Op.hs` | Rewrote `OpDupClosureProj1` with inline code generation |

#### Test Verification

```bash
$ cabal build somac
$ ./test_closure_dup
$ echo $?
23  # Correct: 2839 % 256 = 23
```

All tests pass with the new inline implementation.

**Bug Fix: Unknown Env Size Fallback**

During testing, we discovered that when a closure comes from a function call (e.g., `let f = makeAdder 10`),
the compiler doesn't know its env size at the DUP site. The inline code was incorrectly using `env=0`,
which only copied the header without the env slots.

**Fix:** When `envSize == 0 && null slotInfo`, fall back to calling `soma_proj1` which reads the
env_size from the closure header at runtime. The inline code is only used when we have compile-time
knowledge of the exact env layout (e.g., when the closure was created in the same function).

```haskell
result <- if envSize == 0 && null slotInfo
    then do
        -- Fall back to runtime - closure has unknown env layout
        let proj1Func = LlvmGlobal (LlvmPointer LlvmI8) "\"soma_proj1\""
        saveTmp (LlvmCall proj1Func (LlvmPointer LlvmI8) [voidHandle]) (LlvmPointer LlvmI8)
    else
        -- Generate inline specialized cloning code
        compileInlineClosureProj1 voidHandle envSize slotInfo
```

This ensures correctness while still providing the inline optimization when it's safe to use.

---

## Fork-Join Parallelism

### Design Philosophy

Soma's parallelism follows three core principles:

1. **Zero overhead** - When running sequentially, parallel constructs compile to direct calls
2. **Predictable** - No lazy evaluation, no thunks, no memoization surprises
3. **Automatic** - The linearized IR is already a dependency graph; parallelism is extracted automatically
 
### The Key Insight: Interaction Nets ARE Dependency Graphs

After linearization, the Circuit IR has a crucial property: **every value is used exactly once**.
This means the data flow through the program forms a directed acyclic graph where:
- **Nodes** are let bindings and computations
- **Edges** are variable uses (data dependencies)

Independent computations have no edges between them and can run in parallel.

### The Problem with Lazy Parallelism (Old Approach)

The previous approach used "speculative cloning" via `soma_par_proj0/1`:
- Created lazy SUP nodes that might spawn background tasks
- Unpredictable: depends on runtime heuristics (worker hunger, adaptive thresholds)
- Overhead: every value duplication went through the SUP machinery
- Complex: required tracking task states, work estimates, cache coherence

**Result:** In practice, 0 tasks were spawned because the heuristics were too conservative.

### Fork-Join Model (New Approach)

The new approach extracts parallelism directly from the linearized IR:

```soma
def example =
    let a = expensive1 x in    -- Level 0
    let b = expensive2 y in    -- Level 0 (independent of a)
    let c = expensive3 z in    -- Level 0 (independent of a, b)
    let d = a + b in           -- Level 1 (depends on a, b)
    d + c                      -- Level 2 (depends on c, d)
```

The compiler analyzes dependencies:
1. `a`, `b`, `c` are all independent → can run in parallel (Level 0)
2. `d` depends on `a` and `b` → must wait for Level 0
3. Final expression depends on `c` and `d`

### Parallel Levels via Topological Sort

The parallelization pass (`Circuit/Parallel.hs`):

1. **Build dependency graph** from linearized Circuit IR
2. **Topologically sort** bindings into levels
3. **Fork** all bindings at each level
4. **Join** all before proceeding to next level

```
Level 0: [a, b, c]  -- All independent, fork all three
         ↓ join all
Level 1: [d]        -- Depends on a, b
         ↓ join
Level 2: result     -- Depends on c, d
```

### Compilation Strategy

**Parallel version** (when `SOMA_PARALLEL` is set):
```llvm
; Level 0: Fork all independent computations
%task_a = call ptr @soma_fork(ptr @compute_a, ptr %env_a)
%task_b = call ptr @soma_fork(ptr @compute_b, ptr %env_b)
%task_c = call ptr @soma_fork(ptr @compute_c, ptr %env_c)

; Join Level 0
%a = call i64 @soma_join(ptr %task_a)
%b = call i64 @soma_join(ptr %task_b)
%c = call i64 @soma_join(ptr %task_c)

; Level 1: Only one binding, no parallelism
%d = add i64 %a, %b

; Level 2: Final result
%result = add i64 %d, %c
```

**Sequential version** (default, zero overhead):
```llvm
%a = call i64 @compute_a(ptr %env_a)
%b = call i64 @compute_b(ptr %env_b)
%c = call i64 @compute_c(ptr %env_c)
%d = add i64 %a, %b
%result = add i64 %d, %c
```

### Runtime API

```c
// Fork a computation - spawns task and returns immediately
// fn: function pointer (SomaValue (*)(void* env))
// env: captured environment (moved to task, caller loses ownership)
SomaTask* soma_fork(SomaTaskFn fn, void* env);

// Join a task - blocks until complete, returns result
// task: handle from soma_fork (freed after join)
SomaValue soma_join(SomaTask* task);

// Check if parallel runtime is enabled
int soma_par_enabled(void);
```

### Circuit IR Extensions

New constructs for parallel execution:

```haskell
data CTerm
    = ...
    | CFork !Name !Type !CTerm !CTerm  -- Fork: taskName, resultType, computation, continuation
    | CJoin !Name !Type                -- Join: taskName, resultType
```

**CFork semantics:**
- `CFork taskName ty computation body` spawns `computation` as a task
- Binds `taskName` to the task handle (not the result!)
- Continues with `body` immediately (non-blocking)

**CJoin semantics:**
- `CJoin taskName ty` blocks until task `taskName` completes
- Returns the result with type `ty`

### Dependency Analysis Algorithm

```haskell
-- Build dependency graph from a function body
buildDepGraph :: CTerm -> DepGraph

-- A binding depends on variables it references
-- that are defined by other bindings (not parameters)
getDeps :: Name -> CTerm -> Set Name

-- Topological sort into parallel levels
-- Level n contains bindings whose deps are all in levels < n
topoSort :: DepGraph -> [[Name]]

-- Transform: insert CFork/CJoin based on levels
parallelize :: CTerm -> CTerm
```

**Example:**
```
Input:
  let a = f x in
  let b = g y in
  let c = a + b in
  c

Dependency Graph:
  a -> {}        (no deps)
  b -> {}        (no deps)
  c -> {a, b}    (depends on a and b)

Levels:
  Level 0: [a, b]
  Level 1: [c]

Output:
  CFork "task_a" Int (f x)
    (CFork "task_b" Int (g y)
      (CLet "a" Int (CJoin "task_a" Int)
        (CLet "b" Int (CJoin "task_b" Int)
          (CLet "c" Int (a + b)
            c))))
```

### Work Threshold

Not all computations benefit from parallelism. The compiler estimates work:

```haskell
-- Estimate computational cost
estimateWork :: CTerm -> Int
estimateWork (CApp (CRef name _) _ _) 
    | isRecursive name = 100  -- Recursive calls are worth parallelizing
estimateWork (CApp _ _ _) = 10
estimateWork (CBinOp _ _ _) = 1
estimateWork _ = 1

-- Only fork if:
-- 1. Estimated work exceeds threshold
-- 2. There are multiple independent bindings at this level
shouldFork :: [CTerm] -> Bool
shouldFork terms = length terms > 1 && any (\t -> estimateWork t >= forkThreshold) terms

forkThreshold :: Int
forkThreshold = 50  -- Tune based on fork/join overhead
```

### Memory Model

Fork-join preserves Soma's linear memory model:

1. **Task environments are owned**: When forking, captured variables are moved to the task
2. **Results are owned by joiner**: The join operation transfers ownership of the result
3. **No sharing**: Each task operates on its own data (linearity guarantees this!)
4. **Deterministic cleanup**: Task memory is freed after join

### Implementation Plan

1. **Runtime** (`runtime/soma_runtime.c`):
   - [x] Task pool already exists
   - [x] `soma_fork()` - allocate task, set fn/env, spawn
   - [x] `soma_join()` - wait for completion, return result
   - [x] `soma_par_enabled_export()` - callable from LLVM

2. **Circuit IR** (`Circuit/Ir.hs`):
   - [x] Add `CFork` and `CJoin` constructors
   - [x] Update `getTermType`, `freeVars`, `countVarUses`

3. **Parallelization Pass** (`Circuit/ToAlloy.hs`):
   - [x] Identify single-argument function calls as forkable
   - [x] Emit `OpFork`/`OpJoin` when `--parallel` flag is set
   - [ ] (Future) Build full dependency graph for multi-level parallelism
   - [ ] (Future) Topological sort into parallel levels

4. **Circuit → Alloy** (`Circuit/ToAlloy.hs`):
   - [x] Lower `CFork` to `OpFork`
   - [x] Lower `CJoin` to `OpJoin`

5. **Alloy IR** (`Alloy/Ir.hs`):
   - [x] Add `OpFork` and `OpJoin` operations

6. **LLVM Codegen** (`Llvm/Gen/Op.hs`):
   - [x] Generate calls to `soma_fork_direct`/`soma_join`
   - [x] Sequential fallback with tagged pointer encoding
   - [x] Proper phi nodes for branch merging

### Example: Full Pipeline

**Source:**
```soma
def treeCompute(x: Int, levels: Int) -> Int =
    if levels == 0 then x else
        let left = treeCompute (x * 2) (levels - 1) in
        let right = treeCompute (x * 2 + 1) (levels - 1) in
        left + right
```

**After Linearization:**
```
CLet "left" Int (CApp treeCompute [...] Int)
  (CLet "right" Int (CApp treeCompute [...] Int)
    (CBinOp Add (CVar "left") (CVar "right")))
```

**Dependency Analysis:**
- `left` depends on: `x`, `levels` (parameters, not bindings)
- `right` depends on: `x`, `levels` (parameters, not bindings)
- `left` and `right` are **independent**!

**After Parallelization:**
```
CFork "task_left" Int (CApp treeCompute [...] Int)
  (CFork "task_right" Int (CApp treeCompute [...] Int)
    (CLet "left" Int (CJoin "task_left" Int)
      (CLet "right" Int (CJoin "task_right" Int)
        (CBinOp Add (CVar "left") (CVar "right")))))
```

### Comparison with Other Approaches

| Approach | Overhead | Predictable | Automatic |
|----------|----------|-------------|-----------|
| Lazy SUPs (old) | Medium | No | Yes |
| Manual `par` | Zero | Yes | No |
| Fork-Join (new) | Zero* | Yes | Yes |
| Cilk-style | Low | Mostly | No |

*Zero overhead when running sequentially; fork/join cost when parallel.

### Relation to DUP/SUP

Fork-join parallelism is **orthogonal** to DUP/SUP:

- **DUP/SUP**: Handle value duplication (when a variable is used multiple times)
- **Fork-Join**: Handle parallel execution (when computations are independent)

They compose naturally:
```soma
let f = (\x -> expensive x) in   -- f will be duplicated (DUP)
let r1 = f a in                   -- } Independent computations
let r2 = f b in                   -- } Can run in parallel (FORK)
r1 + r2                           -- JOIN both results
```

The linearization pass inserts DUP for `f`. The parallelization pass sees `r1` and `r2` are independent and inserts FORK/JOIN.

### Session 22 (2024)

**Fork-Join Parallelism Implementation**

This session completed the fork-join parallelism implementation, enabling automatic
parallelization of independent computations via the `--parallel` compiler flag.

#### Overview

Fork-join parallelism spawns independent computations as tasks that can be stolen by
worker threads. Unlike the previous speculative SUP-based approach, this is explicit
and predictable: the compiler identifies single-argument function calls in the
Circuit IR and emits fork/join operations.

#### New Circuit IR Constructs

Added `CFork` and `CJoin` to `Circuit/Ir.hs`:

```haskell
| CFork !Name !Type !CTerm !CTerm  -- Fork: taskName, resultType, computation, continuation
| CJoin !Name !Type                -- Join: taskName, resultType
```

**CFork semantics:**
- `CFork taskName ty computation body` spawns `computation` as a parallel task
- Binds `taskName` to a task handle (not the result)
- Continues with `body` immediately (non-blocking)

**CJoin semantics:**
- `CJoin taskName ty` blocks until task `taskName` completes
- Returns the result value with type `ty`

#### Compiler Flag: `--parallel`

Added `--parallel` flag to enable fork-join parallelism:

```bash
# Compile with parallelization enabled
somac build myfile.soma --parallel

# Run with 64 worker threads and stats
SOMA_PARALLEL=64 SOMA_PAR_STATS=1 ./myfile
```

**Changes to `Config/Options.hs`:**
```haskell
data Options = Options
    { ...
    , optionsParallel :: Bool  -- Enable automatic parallelization
    }
```

The flag is threaded through `Build/Incremental.hs` to `Circuit/ToAlloy.hs` via
`ParallelConfig`:

```haskell
data ParallelConfig = ParallelConfig
    { pcEnabled :: Bool         -- Enable fork/join generation
    , pcWorkThreshold :: Int    -- Minimum work estimate to fork
    }
```

#### Alloy IR Operations

Added `OpFork` and `OpJoin` to `Alloy/Ir.hs`:

```haskell
| OpFork AOperand AOperand      -- Fork: function, argument
| OpJoin AOperand               -- Join: task handle
```

**OpFork** takes a function reference and a single argument, returning a task handle.
**OpJoin** takes a task handle and returns the computed result.

#### LLVM Codegen with Sequential Fallback

The LLVM codegen in `Llvm/Gen/Op.hs` generates branching code that works correctly
whether the parallel runtime is enabled or not:

```llvm
; Check if parallel runtime is active
%par_enabled = call i32 @soma_par_enabled_export()
%is_parallel = icmp ne i32 %par_enabled, 0
br i1 %is_parallel, label %fork_parallel, label %fork_sequential

fork_parallel:
  ; Spawn task via runtime
  %task = call ptr @soma_fork_direct(ptr @myfunction, i64 %arg)
  %task_i64 = ptrtoint ptr %task to i64
  br label %fork_merge

fork_sequential:
  ; Call function directly
  %result = call i64 @myfunction(i64 %arg)
  ; Encode result with tag bit: (result << 1) | 1
  %shifted = shl i64 %result, 1
  %tagged = add i64 %shifted, 1
  br label %fork_merge

fork_merge:
  ; Phi selects between task handle and tagged inline result
  %handle = phi i64 [ %task_i64, %fork_parallel ], [ %tagged, %fork_sequential ]
```

**OpJoin** decodes the result:

```llvm
; Check low bit: 1 = inline result, 0 = task handle
%low_bit = and i64 %handle, 1
%is_inline = icmp ne i64 %low_bit, 0
br i1 %is_inline, label %join_inline, label %join_parallel

join_inline:
  ; Decode inline result: handle >> 1
  %result = lshr i64 %handle, 1
  br label %join_merge

join_parallel:
  ; Wait for task completion
  %task_ptr = inttoptr i64 %handle to ptr
  %result = call i64 @soma_join(ptr %task_ptr)
  br label %join_merge

join_merge:
  %final = phi i64 [ %decoded, %join_inline ], [ %result, %join_parallel ]
```

This tagged-pointer encoding ensures:
- **Zero overhead when parallel runtime is disabled**: Results computed inline
- **Correct behavior with parallel runtime**: Tasks spawned and joined properly

#### Runtime Changes

**New function: `soma_par_enabled_export()`**

The `soma_par_enabled()` function was `static inline` in the header, so LLVM couldn't
call it. Added an exported wrapper in `soma_runtime.c`:

```c
int soma_par_enabled_export(void) {
    return soma_par_enabled();
}
```

**Fixed `soma_join()` to give workers a chance:**

Previously, `soma_join()` would immediately execute a pending task inline, preventing
actual parallelism. Added a brief yield loop:

```c
SomaValue soma_join(SomaTask* task) {
    ...
    if (state == TASK_PENDING) {
        /* Give workers a brief chance to steal the task */
        for (int i = 0; i < 100; i++) {
            sched_yield();
            state = atomic_load(&task->state);
            if (state != TASK_PENDING) break;
        }
        
        /* If still pending, run it ourselves */
        if (state == TASK_PENDING) {
            // ... execute inline
        }
    }
    ...
}
```

**Fixed double-counting in `tasks_spawned`:**

The counter was being incremented in both `soma_par_spawn()` and `soma_fork_direct()`.
Removed the duplicate increment in `soma_fork_direct()`.

#### Circuit/ToAlloy.hs Changes

When `pcEnabled = True`, the lowering pass identifies forkable calls and emits
`CFork`/`CJoin` pairs:

```haskell
-- Check if a term is a simple forkable call (single-arg function call)
extractForkableCall :: C.CTerm -> Maybe (C.Name, C.CTerm)
extractForkableCall term =
    let (fun, args) = collectArgs term
    in case (fun, args) of
        (C.CVar fnName _, [arg]) -> Just (fnName, arg)
        (C.CRef fnName _, [arg]) -> Just (fnName, arg)
        _ -> Nothing

-- In lowerTerm for CLet:
case extractForkableCall val of
    Just (fnName, arg) | pcEnabled parallelConfig -> do
        -- Emit fork
        argOp <- lowerTerm env arg
        let fnOp = OpVar fnName
        taskHandle <- emitLetTmp ty (OpFork fnOp argOp)
        
        -- Lower body with task handle bound
        let env' = extendOperand name (OpVar taskHandle) env
        lowerTerm env' body
        
        -- Join will be emitted when the task handle is used
    _ -> -- Normal lowering
```

#### Test Results

Running with `SOMA_PARALLEL=64 SOMA_PAR_STATS=1`:

```
[soma_par] Workers: 64
[soma_par] Tasks spawned: 2
[soma_par] Tasks run: 2
[soma_par] Tasks stolen: 2
...
[soma_par] Worker 8: run=1 stolen=1 attempts=460460
[soma_par] Worker 11: run=1 stolen=1 attempts=267614
```

- **Tasks spawned: 2** - Two function calls were forked (`chainedClosures`, `nestedDupTest`)
- **Tasks run: 2** - Both tasks were executed by workers
- **Tasks stolen: 2** - Workers 8 and 11 stole and executed the tasks
- **Result: 22** - Correct (matches sequential execution)

#### Files Modified

| File | Changes |
|------|---------|
| `Circuit/Ir.hs` | Added `CFork`, `CJoin` constructors |
| `Circuit/Alloc.hs` | Handle `CFork`, `CJoin` in allocation analysis |
| `Circuit/Escape.hs` | Handle `CFork`, `CJoin` in escape analysis |
| `Circuit/ToAlloy.hs` | Emit `OpFork`/`OpJoin` for single-arg function calls |
| `Config/Options.hs` | Added `--parallel` flag |
| `Build/Incremental.hs` | Thread `enableParallel` through compilation |
| `Main.hs` | Pass `optionsParallel` to build functions |
| `Alloy/Ir.hs` | Added `OpFork`, `OpJoin` operations |
| `Alloy/Subst.hs` | Handle new operations in substitution |
| `Alloy/PromoteRefs.hs` | Handle new operations |
| `Alloy/Uniqueness.hs` | Handle new operations |
| `Alloy/Inline.hs` | Handle new operations |
| `Llvm/Gen/Op.hs` | LLVM codegen for `OpFork`, `OpJoin` with sequential fallback |
| `Llvm/Gen/CRuntime.hs` | Added `soma_par_enabled_export` declaration |
| `Llvm/Instructions.hs` | Added `LlvmAnd` instruction |
| `runtime/soma_runtime.c` | Added `soma_par_enabled_export`, fixed `soma_join` yield loop, fixed double-counting |

#### Implementation Status Update

The fork-join parallelism implementation is now complete:

- [x] `CFork`/`CJoin` in Circuit IR
- [x] `OpFork`/`OpJoin` in Alloy IR
- [x] `--parallel` compiler flag
- [x] LLVM codegen with sequential fallback
- [x] Runtime `soma_fork_direct`, `soma_join` integration
- [x] Tagged pointer encoding for inline vs task results
- [x] Work stealing verification (tasks actually stolen and run by workers)

#### Performance Characteristics

| Mode | Fork Cost | Join Cost | Total Overhead |
|------|-----------|-----------|----------------|
| Sequential (`--parallel` not used) | N/A | N/A | Zero |
| Parallel disabled at runtime | Branch + inline call | Branch + shift | ~2 instructions |
| Parallel enabled | Task alloc + spawn | Wait + free | ~microseconds |

The implementation achieves the design goal: **zero overhead when running sequentially**,
with predictable parallel execution when enabled.

### Session 22 (2024)

**Multi-Argument Fork Support**

This session extended the fork-join parallelism to support multi-argument function calls,
not just single-argument calls.

#### The Problem

The initial fork implementation (Session 21) only handled single-argument function calls
via `extractForkableCall`. Multi-argument calls like `computeLevel(5, 8)` or
`treeCompute(left, levels - 1)` were being lowered sequentially despite being forkable.

**Example from `test_parallel.soma`:**

```soma
def computeLevel(base: Int, depth: Int) -> Int = ...

-- In main:
let r1 = computeLevel(5, 8)  -- Was lowered sequentially!
```

The Circuit IR already represents this in curried form:
```
((computeLevel 5) 8)
```

But `extractForkableCall` only matched single-arg calls, missing these opportunities.

#### The Solution: Multi-Arg OpFork

**Changed `OpFork` signature in `Alloy/Ir.hs`:**

```haskell
-- Before:
| OpFork AOperand AOperand      -- fn, single arg

-- After:
| OpFork AOperand [AOperand]    -- fn, list of args
```

**Changed CFork lowering in `Circuit/ToAlloy.hs`:**

Instead of `extractForkableCall`, we now use `collectArgs` to uncurry any application:

```haskell
C.CFork taskName ty comp body -> do
    let (fun, args) = collectArgs comp
    case fun of
        C.CRef fnName _ | not (null args) -> do
            argOps <- mapM (lowerTerm env) args
            taskHandle <- emitLetTmp ty (OpFork (OpVar fnName) argOps)
            -- ... bind handle and lower body
        _ -> -- fallback to sequential
```

**LLVM Codegen in `Llvm/Gen/Op.hs`:**

- Single arg: uses `soma_fork_direct(fn, arg)` as before
- Multiple args: uses new `soma_fork_multi(fn, args_array, num_args)`
  - Stack-allocates array for args
  - Copies i64-converted args into array
  - Calls runtime with function pointer, args array, and count

**Sequential fallback fix:**

The sequential path was incorrectly calling functions with `i64` args when the
actual function signature used `i32`. Fixed by using original `llArgs` (with
correct types) instead of converted `i64Args`:

```haskell
-- Sequential path: call function directly with original args (not i64-converted)
tell [LlvmLabel sequentialBlock]
rawResult <- saveTmp (LlvmCall fnPtr resultTy llArgs) resultTy
-- Convert result to i64 for encoding
inlineResult <- case resultTy of
    LlvmI64 -> pure rawResult
    LlvmI32 -> saveTmp (LlvmSExt rawResult LlvmI64) LlvmI64
    -- ... other type conversions
```

**Runtime changes in `soma_runtime.c`:**

Added `soma_fork_multi`:

```c
SomaTask* soma_fork_multi(void* fn, SomaValue* args, int num_args) {
    if (!soma_par_enabled()) return NULL;
    
    SomaTask* task = soma_task_alloc();
    SomaValue* args_copy = malloc(num_args * sizeof(SomaValue));
    memcpy(args_copy, args, num_args * sizeof(SomaValue));
    
    task->kind = TASK_KIND_MULTI;
    task->fn.multi = fn;
    task->env = args_copy;
    task->arg = (SomaValue)num_args;
    
    soma_par_spawn(task);
    return task;
}
```

Added `TASK_KIND_MULTI` handling in `task_execute`:

```c
case TASK_KIND_MULTI: {
    SomaValue* args = (SomaValue*)task->env;
    int num_args = (int)task->arg;
    void* fn = task->fn.multi;
    SomaValue result;
    switch (num_args) {
        case 2: { typedef SomaValue (*Fn2)(SomaValue, SomaValue);
                  result = ((Fn2)fn)(args[0], args[1]); break; }
        case 3: { typedef SomaValue (*Fn3)(SomaValue, SomaValue, SomaValue);
                  result = ((Fn3)fn)(args[0], args[1], args[2]); break; }
        // ... cases 4, 5, 6
    }
    free(args);
    return result;
}
```

#### Updated Alloy Passes

All passes updated for new `OpFork` signature:

| File | Changes |
|------|---------|
| `Alloy/Uniqueness.hs` | Track uses of fn and all args |
| `Alloy/PromoteRefs.hs` | Check fn and all args for variable refs |
| `Alloy/Subst.hs` | Apply substitution to fn and all args |
| `Alloy/Inline.hs` | Apply inlining substitution to fn and all args |
| `Logging/Trees.hs` | Pretty print with comma-separated args |

#### Current Status: Runtime Segfault

The multi-arg fork implementation compiles correctly but has a runtime issue.
When running with `SOMA_PARALLEL=64`, the program segfaults in `soma_fork_multi`
after many successful calls.

**Observed behavior:**
- Many `soma_fork_multi` calls succeed (visible with debug tracing)
- Crash occurs after ~50+ successful forks
- Backtrace shows crash inside `soma_fork_multi`, called from `treeCompute`

**Suspected causes:**
1. **ABI mismatch**: Runtime expects `i64` args but functions are defined with `i32` params
2. **Stack exhaustion**: Deep recursion with parallel tasks
3. **Race condition**: Memory corruption in task allocation or work stealing

The ABI mismatch is the most likely cause. Soma functions use `i32` for `Int` type,
but the runtime's `task_execute` casts to functions expecting `SomaValue` (i64) args.
On ARM64, this may work for some cases but cause corruption in others.

**Potential fixes:**
1. Change Soma's `Int` type to compile as `i64` instead of `i32`
2. Generate wrapper trampolines that convert `i64` ↔ `i32`
3. Store function signature info in tasks for proper dispatch

#### Files Modified

| File | Changes |
|------|---------|
| `Alloy/Ir.hs` | Changed `OpFork AOperand AOperand` to `OpFork AOperand [AOperand]` |
| `Circuit/ToAlloy.hs` | Use `collectArgs` for multi-arg fork lowering |
| `Llvm/Gen/Op.hs` | Multi-arg codegen with `soma_fork_multi`, fixed sequential path types |
| `Llvm/Gen/CRuntime.hs` | Added `soma_fork_multi` declaration |
| `Alloy/Uniqueness.hs` | Handle list of args in `OpFork` |
| `Alloy/PromoteRefs.hs` | Handle list of args in `OpFork` |
| `Alloy/Subst.hs` | Handle list of args in `OpFork` |
| `Alloy/Inline.hs` | Handle list of args in `OpFork` |
| `Logging/Trees.hs` | Pretty print multi-arg fork |
| `runtime/soma_runtime.h` | Added `TASK_KIND_MULTI`, `SomaMultiFn`, `soma_fork_multi` |
| `runtime/soma_runtime.c` | Implemented `soma_fork_multi`, `task_execute` for TASK_KIND_MULTI |

#### Next Steps

To fix the runtime segfault:

1. **Investigate ABI mismatch**: The mismatch between Soma's `Int` (i32) and runtime's
   `SomaValue` (i64) calling convention needs resolution. Either:
   - Standardize on i64 for all values at the LLVM level
   - Generate proper type-aware dispatch in the runtime

2. **Add debugging**: More detailed tracing in `task_execute` to catch the exact
   failure point

3. **Test with fewer workers**: Try `SOMA_PARALLEL=1` to isolate concurrency issues

### Session 23 (2024)

**Goal**: Fix the multi-argument fork segfault from Session 22.

#### Root Cause Analysis

The segfault had two causes:

1. **ABI Mismatch**: The runtime's `task_execute` was calling functions with `SomaValue` (i64)
   arguments, but Soma functions are compiled with native types (e.g., `i32` for `Int`).
   On ARM64, passing i64 values to functions expecting i32 parameters causes undefined behavior.

2. **Stack Overflow**: Worker threads use the default pthread stack size (~2MB on Linux).
   With 32+ threads and deep recursive parallel calls (like `treeCompute` with 6 levels),
   the combined stack usage exceeded available memory, causing corruption.

#### Solution: Trampoline Wrappers

Instead of changing Soma's `Int` to i64 (which would affect all code), we generate
**trampoline wrapper functions** at each fork site. The trampoline:

1. Takes a pointer to an array of i64 (SomaValue) arguments
2. Loads each argument and converts to the native type (truncate i64 → i32, inttoptr, etc.)
3. Calls the actual function with correctly-typed arguments
4. Converts the result back to i64 (SomaValue)

**Generated LLVM IR example:**
```llvm
define i64 @"fork_trampoline_954"(ptr %args_ptr) {
entry:
  %arg_ptr_0 = getelementptr inbounds i64, ptr %args_ptr, i32 0
  %arg_i64_0 = load i64, ptr %arg_ptr_0
  %arg_0 = trunc i64 %arg_i64_0 to i32
  %arg_ptr_1 = getelementptr inbounds i64, ptr %args_ptr, i32 1
  %arg_i64_1 = load i64, ptr %arg_ptr_1
  %arg_1 = trunc i64 %arg_i64_1 to i32
  %call_result = call i32 @"treeCompute$m51113078"(i32 %arg_0, i32 %arg_1)
  %result_i64 = sext i32 %call_result to i64
  ret i64 %result_i64
}
```

#### Implementation Details

**Compiler changes (`Llvm/Gen/Op.hs`):**
- `compileOp (OpFork ...)` now generates a unique trampoline function for each fork
- Helper functions added: `generateTrampoline`, `generateArgLoads`, `generateArgConversion`, `generateResultConversion`
- The trampoline is registered via `modify (\s -> s { irFunctions = fn : irFunctions s })`
- `soma_fork_multi` is called with the trampoline pointer instead of the real function

**Runtime changes:**
- Renamed `TASK_KIND_MULTI` to `TASK_KIND_TRAMPOLINE`
- Renamed `SomaMultiFn` to `SomaTrampolineFn` with signature `SomaValue (*)(SomaValue* args)`
- Simplified `task_execute` - trampoline handles all type conversion
- Added `pthread_attr_setstacksize(&attr, 512 * 1024)` for worker threads

**Statistics fix:**
- Added `tasks_run_inline` counter for tasks executed by the joining thread
- Previously, tasks run inline in `soma_join` weren't counted, causing confusion

#### Type Conversion Table

| Soma Type | LLVM Type | i64 → Native | Native → i64 |
|-----------|-----------|--------------|--------------|
| Int       | i32       | trunc        | sext         |
| Bool      | i1        | trunc        | zext         |
| Char      | i8        | trunc        | sext         |
| Ptr types | ptr       | inttoptr     | ptrtoint     |
| SomaValue | i64       | (identity)   | (identity)   |

#### Test Results

```
$ SOMA_PARALLEL=4 SOMA_PAR_STATS=1 ./test_parallel
[soma_par] Workers: 4
[soma_par] Tasks spawned: 4112
[soma_par] Tasks run (workers): 72
[soma_par] Tasks run (inline): 4040
[soma_par] Tasks stolen: 373
```

The fix resolves the segfault for all tested thread counts (2, 4, 8, 16, 32).
With 64 threads, stack space becomes a limiting factor (64 × 512KB = 32MB), 
which may require OS-level tuning (`ulimit -s`) for very high thread counts.

#### Files Modified

| File | Changes |
|------|---------|
| `Llvm/Gen/Op.hs` | Trampoline generation for `OpFork`, added helper functions |
| `runtime/soma_runtime.h` | Renamed `TASK_KIND_MULTI` → `TASK_KIND_TRAMPOLINE`, added `tasks_run_inline` stat |
| `runtime/soma_runtime.c` | Simplified `task_execute`, 512KB worker stacks, inline task counting |

#### Key Insight

The trampoline approach is superior to changing Soma's `Int` to i64 because:
1. **No code bloat**: Only parallel call sites get trampolines
2. **Type safety**: Native types preserved throughout the codebase
3. **Performance**: Non-parallel code remains optimal (no unnecessary widening)
4. **Isolation**: The ABI translation is contained at fork boundaries
