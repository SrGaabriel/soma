# 🚀 soma

Soma is a statically-typed, pure functional language with Hindley–Milner style type inference and a practical, performance-minded compiler.

---

## ✨ Overview

Soma aims to give you readable, expressive code while the compiler handles specialization and optimization up front. It is statically typed (Hindley–Milner), evaluates eagerly (so memory and CPU behavior are easier to predict), and models effects explicitly so the optimizer can treat most code as pure.

The compiler turns high-level functional patterns into efficient first-order code using lambda-lifting, specialization (monomorphization), and targeted inlining. Through its Circuit IR backend, Soma achieves optimal evaluation via Interaction Nets—delivering GC-free memory management with deterministic lifetimes. The user writes normal functional code; the compiler infers linearity, inserts explicit duplication and erasure nodes, and generates code that frees memory at the exact point of consumption.

Put simply: write composable, declarative code; the compiler does the heavy lifting to make it run like systems code—without garbage collection pauses.

---

## 💡 Examples

You can find some examples in the `examples/` directory. They are not comprehensive, but should give you a taste of the language and its syntax.

---

## 🛠️ Compiler backend breakdown

The compiler provides three compilation modes, each optimized for different use cases:

### Three Compilation Modes

Use the `-m` / `--mode` flag to select:

1. **Standard Mode** (`-m standard`) - Default, predictable runtime (no laziness or implicit parallelism)
2. **Hybrid Mode** (`-m hybrid`) - Native but parallelized with fork-join on hot paths
3. **Graph Mode** (`-m graph`) - Full interaction net reduction with work-stealing parallelism

### Native Mode Pipeline

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

Same as Native mode but with fork-join parallelism enabled via compiler analysis:

1-3. **Same as Native** (Metal → Circuit → Linearization)

4. **Parallelization 🔀**: Before LTO, the compiler inserts fork/join operations at hot paths detected via work estimation heuristics. Enable at runtime with `SOMA_PARALLEL=N` where N is worker count.

5-7. **Same as Native** (Alloy → LTO → LLVM)

**Runtime**: `hybrid_soma.a` - Wraps native runtime with optional parallel work-stealing scheduler.

### Graph Mode Pipeline

Full interaction net graph reduction with automatic parallelism:

1. **Metal (HIR) 🧱**: Same high-level IR, preserving full System F-Omega polymorphism and higher-kinded types.

2. **Circuit IR 🔄**: Same interaction net IR as Native mode, but **no linearization**. The Circuit IR remains non-affine; the runtime handles duplication lazily via graph reduction.

3. **Graph Lowering 🕸️**: Circuit IR is lowered directly to Alloy's graph operations (`OpGraphNum`, `OpGraphRef`, `OpGraphAdd`, etc.). Functions build and return graph structures instead of computing values eagerly.

4. **Alloy (MIR) 📋**: Graph-based Alloy IR is optimized (inlining, CSE, etc.).

5. **LTO & LLVM**: Same whole-program optimization and LLVM codegen.

**Runtime**: `inets_soma.a` - Pure interaction net runtime with work-stealing reduction. Achieves up to **8.77x speedup** (4 workers) on recursive workloads via automatic parallelism. Enable with `SOMA_WORKERS=N`.

### Key Benefits of Circuit IR

- **No GC pauses**: Memory is freed deterministically at consumption points (Native/Hybrid)
- **Optimal sharing**: Lazy duplication (HVM-style) avoids recomputation (all modes)
- **Automatic parallelism**: Independent subgraphs reduce in parallel without locks (Graph mode)
- **Predictable performance**: No unpredictable collection pauses, real-time safe (all modes)
- **User choice**: Pick the right tradeoff between predictability (Native), optional parallelism (Hybrid), or automatic parallelism (Graph)

---

# ✨ Etymology

Soma draws its name from three linguistic roots that together capture the language's philosophy:

1. **Portuguese: "soma" (sum/addition):** In mathematics, Σ denotes summation: the composition of many terms into a whole. Soma embraces this compositional spirit: monads chain effects, functions composition, and type classes let you abstract over structure. The syntax reads like notation, letting you build programs as elegant equations where complex behavior emerges from the sum of simple, pure parts.

2. **Sanskrit: सोम (soma):** In Vedic tradition, soma was a sacred elixir extracted through precise, multi-stage refinement—pressed, filtered, distilled—transforming raw plant matter into concentrated divine essence. Soma the language performs an analogous transformation: your high-level functional abstractions passes through each stage refining and concentrating your code's computational power until what emerges is potent, optimized machine code that has shed all inefficiency while preserving its essential purity.

3. **Greek: σῶμα (sôma) (body/substance):** While you compose pure abstractions, Soma provides the material foundation that makes them real. The compiler handles the dirty work giving your ethereal functional code a solid, efficient body that runs on actual hardware.

---

# 🙏 Acknowledgments

Special thanks to **HigherOrderCompany** (HOC) and **Victor Taelin** for their groundbreaking research and development in Interaction Nets and Interaction Calculus. Their work on optimal evaluation, the HVM runtime, and the theoretical foundations of interaction-based computation has been instrumental in shaping Soma's Circuit IR and its approach to GC-free functional programming. The insights from their research have made it possible to achieve optimal reduction without garbage collection while maintaining the expressiveness of pure functional code.
