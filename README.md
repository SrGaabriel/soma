<p style="text-align: center"><img src="docs/assets/icon.png" alt="Soma Logo" width="1024" height="1024"/></p>

# 🚀 soma

Soma is a statically-typed, pure functional language with Hindley–Milner style type inference and a practical, performance-minded compiler.

---

## ✨ Overview

Soma aims to give you readable, expressive code while the compiler handles specialization and optimization up front. It is statically typed (Hindley–Milner), evaluates eagerly (so memory and CPU behavior are easier to predict), and models effects explicitly so the optimizer can treat most code as pure.

The compiler turns high-level functional patterns into efficient first-order code using lambda-lifting, specialization (monomorphization), and targeted inlining. Through its Circuit IR backend, Soma achieves optimal evaluation via Interaction Nets—delivering GC-free memory management with deterministic lifetimes. The user writes normal functional code; the compiler infers linearity, inserts explicit duplication and erasure nodes, and generates code that frees memory at the exact point of consumption.

Put simply: write composable, declarative code; the compiler does the heavy lifting to make it run like systems code—without garbage collection pauses.

---

## 📚 User Guide

Clone the repository and run:

```bash
./install.sh
```

Then:

```bash
somac <source-file>.soma -m <mode>
```

---

## 💡 Examples

You can find some examples in the `examples/` directory. They are not comprehensive, but should give you a taste of the language and its syntax.

---

## 🛠️ Compiler backend breakdown

The compiler provides three compilation modes, each optimized for different use cases:

### Three Compilation Modes

Use the `-m` / `--mode` flag to select:

1. **Standard Mode** (`-m standard`) - Default, predictable runtime (no laziness or implicit parallelism)
2. **Hybrid Mode** (`-m hybrid`) - Standard with fork-join parallelism on hot paths
3. **Graph Mode** (`-m graph`) - Interaction net reduction with compile-time linearization and work-stealing parallelism

### Standard Mode Pipeline

The default compilation path for predictable, sequential execution:

1. **Metal (HIR) 🧱**: After inference, the compiler produces a higher-level IR. This stage performs lambda-lifting (nested functions become explicit top-level closures) and normalization to get a predictable, analyzable shape.

2. **Circuit IR 🔄**: An Interaction Net-based intermediate representation that achieves optimal (Lamping-style) evaluation without garbage collection. The compiler:
   - Infers linearity automatically (no linear types required in source)
   - Inserts explicit DUP nodes where values are used multiple times
   - Inserts explicit ERA nodes where values are discarded
   - Generates code with deterministic memory management—values are freed at their exact point of consumption

3. **Linearization ✂️**: Transforms Circuit IR into affine form where each variable is used exactly once. This gives us precise lifetime information for free: no reference counting, no tracing GC, no cycles.

4. **Alloy (MIR) 📋**: The linearized Circuit IR is lowered to Alloy's CFG-based representation. This mid-level IR applies optimizations: monomorphization, inlining, defunctionalization, CSE, and more.

5. **LTO ⚡**: Separately-compiled modules are fused for whole-program passes. This LTO-style phase enables cross-module monomorphization, inlining, and aggressive specialization.

6. **LLVM 🛡️**: The optimized IR is translated to LLVM IR. From there, standard LLVM tools produce object files or executables.

**Runtime**: `native_soma.a` - Stack + memory pools, predictable sequential execution.

### Hybrid Mode Pipeline

Same as Standard mode but with fork-join parallelism enabled via compiler analysis:

1-3. **Same as Standard** (Metal → Circuit → Linearization)

4. **Parallelization 🔀**: Before LTO, the compiler inserts fork/join operations at hot paths detected via work estimation heuristics. Enable at runtime with `SOMA_WORKERS=N` where N is worker count.

5-7. **Same as Standard** (Alloy → LTO → LLVM)

**Runtime**: `hybrid_soma.a` - Wraps native runtime with optional parallel work-stealing scheduler.

### Graph Mode Pipeline

Interaction net reduction with compile-time linearization and automatic parallelism:

1. **Metal (HIR) 🧱**: Same high-level IR, preserving full System F-Omega polymorphism and higher-kinded types.

2. **Circuit IR 🔄**: Same interaction net IR as Standard mode.

3. **Linearization ✂️**: Transforms to affine form with compile-time DUP placement. This allows type-based specialization—primitives bypass graph overhead entirely.

4. **Graph Lowering 🕸️**: Linearized Circuit IR is lowered to Alloy's graph operations. The compiler knows statically where duplication occurs and can specialize: primitives use direct operations, complex types use the interaction net runtime.

5. **Alloy (MIR) 📋**: Graph-based Alloy IR is optimized (inlining, CSE, etc.).

6. **LTO & LLVM**: Same whole-program optimization and LLVM codegen.

**Runtime**: `inets_soma.a` - Interaction net runtime with compile-time duplication placement and work-stealing reduction. Achieves up to **8.77x speedup** (4 workers) on recursive workloads via automatic parallelism. Enable with `SOMA_WORKERS=N`.

### Key Benefits of Circuit IR

- **No GC pauses**: Memory is freed deterministically at consumption points (Standard/Hybrid)
- **Optimal sharing**: Interaction net reduction avoids recomputation (Graph mode)
- **Compile-time specialization**: Type-based optimization eliminates overhead for primitives (Graph mode)
- **Automatic parallelism**: Independent subgraphs reduce in parallel without locks (Graph mode)
- **Predictable performance**: No unpredictable collection pauses, real-time safe (all modes)
- **User choice**: Pick the right tradeoff between predictability (Standard), optional parallelism (Hybrid), or automatic parallelism (Graph)

# ✨ Etymology

Soma draws its name from three linguistic roots that together capture the language's philosophy:

1. **Portuguese: "soma" (sum/addition):** In mathematics, Σ denotes summation: the composition of many terms into a whole. Soma embraces this compositional spirit: monads chain effects, functions composition, and type classes let you abstract over structure. The syntax reads like notation, letting you build programs as elegant equations where complex behavior emerges from the sum of simple, pure parts.

2. **Sanskrit: सोम (soma):** In Vedic tradition, soma was a sacred elixir extracted through precise, multi-stage refinement—pressed, filtered, distilled—transforming raw plant matter into concentrated divine essence. Soma the language performs an analogous transformation: your high-level functional abstractions passes through each stage refining and concentrating your code's computational power until what emerges is potent, optimized machine code that has shed all inefficiency while preserving its essential purity.

3. **Greek: σῶμα (sôma) (body/substance):** While you compose pure abstractions, Soma provides the material foundation that makes them real. The compiler handles the dirty work giving your ethereal functional code a solid, efficient body that runs on actual hardware.

---

# ⚖️ Comparison to Other Languages

Soma occupies a unique position: **pure functional programming without garbage collection**. Here's how it compares to alternatives:

## vs. HVM / Bend

**HVM and Bend** achieve theoretical optimality through lazy evaluation and runtime graph reduction, maximizing lambda sharing.

**Soma** uses **strict (call-by-value) evaluation** by design:
- **Predictable performance**: No hidden thunks, no lazy overhead
- **Deterministic memory**: Values freed at consumption point
- **Real-time safe**: No GC pauses, bounded allocation
- **Simple cost model**: What you see is what you compute

Soma achieves **practical optimality** through compile-time linearization (static DUP placement), type-based specialization (primitives never touch the graph), and eager interaction nets (optimal reduction without lazy overhead).

**Use HVM/Bend if:** You need maximal laziness and theoretical optimality above all.  
**Use Soma if:** You need strict evaluation, deterministic memory, and no GC pauses.

## vs. Haskell

**Haskell** is the gold standard for pure functional programming, with decades of research, lazy evaluation, and a rich ecosystem.

**Soma** shares Haskell's functional purity but differs in key ways:
- **Strict vs. lazy**: Predictable performance, no space leaks
- **No GC**: Deterministic memory vs. GHC's runtime
- **Simpler syntax**: Less historical baggage, cleaner surface language
- **Modern tooling**: Built-in LSP, fast builds, integrated package manager (vs. Cabal/Stack complexity)

Both support type classes and higher-kinded types. Haskell has a massive ecosystem; Soma prioritizes predictability and systems performance.

**Use Haskell if:** You need the mature ecosystem, laziness, and decades of libraries.  
**Use Soma if:** You need functional purity with no GC pauses and predictable performance.

## vs. Rust

**Rust** achieves systems programming without GC through explicit ownership and the borrow checker.

**Soma** achieves it through functional purity and automatic linearity inference:
- **No borrow checker**: Linearity is inferred, not annotated
- **Functional-first**: Pure abstractions vs. imperative control
- **Different trade-offs**: Expressiveness vs. fine-grained control

**Use Rust if:** You need unsafe FFI, kernel programming, or explicit memory control.  
**Use Soma if:** You want functional purity with systems performance, without fighting a borrow checker.

## vs. OCaml

**OCaml** is a strict functional language with excellent performance and a mature ecosystem.

**Soma** shares OCaml's strict evaluation and functional approach, but:
- **No GC**: Deterministic memory vs. generational GC
- **Interaction nets**: Optimal reduction vs. traditional evaluation
- **Type classes**: vs. module system
- **Work-stealing parallelism**: vs. domain-based parallelism

**Use OCaml if:** You need the mature ecosystem and established tooling.  
**Use Soma if:** You need to eliminate GC pauses (games, real-time, HFT).

## vs. Go

**Go** prioritizes simplicity, fast compilation, and goroutines.

**Soma** offers:
- **Richer type system**: Sum types, pattern matching, generics, type classes
- **No null**: Option/Result types instead of nil
- **Functional purity**: Immutability by default
- **No GC pauses**: Deterministic memory
- **Work-stealing parallelism**: Built into the interaction net runtime

**Use Go if:** You want dead-simple deployment and minimal learning curve.  
**Use Soma if:** You want functional abstractions with predictable performance and no GC.

## vs. Zig

**Zig** is a modern systems language focused on simplicity and C interop, with explicit manual memory management.

**Soma** approaches systems programming from a functional perspective:
- **Functional vs. imperative**: Pure functions vs. manual control
- **Inferred linearity vs. explicit**: Compiler handles lifetimes
- **Different primitives**: Type classes/HOFs vs. comptime

**Use Zig if:** You want explicit control and a C-like experience.
**Use Soma if:** You want functional programming with systems performance.

## The Soma Niche

Soma is for developers who want:
1. **Functional purity** (like Haskell/OCaml)
2. **No garbage collection** (like Rust/Zig)
3. **Strict evaluation** (like OCaml/ML)
4. **Predictable performance** (like Go/Rust)

---

# 🎨 Branding

**Color scheme:**
1. **Primary:** Teal `#1ABC9C`: Not too bright (immature), not too dark (ancient)—represents clarity and balance.
2. **Secondary:** Cerulean Blue `#34495E`: Professional, trustworthy, stable.

---

# 🙏 Acknowledgments

Special thanks to **HigherOrderCo** (HOC) and **Victor Taelin** for their groundbreaking research and development in Interaction Nets and Interaction Calculus. Their work on optimal evaluation, the HVM runtime, and the theoretical foundations of interaction-based computation has been instrumental in developing Soma's Circuit IR and runtime system.
