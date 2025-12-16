# ⚗️ soma

Soma is a statically-typed, pure functional language with Hindley–Milner style type inference, explicit effect modeling, and eager evaluation semantics. It leverages Interaction Nets for optimal evaluation, enabling GC-free memory management with deterministic lifetimes and automatic parallelism.

---

## ✨ Overview

Combining high-level expressiveness with predictable performance characteristics, Soma features System F-ω typing, eager evaluation semantics, and explicit effect modeling to enable aggressive compile.

Soma achieves optimal evaluation via Interaction Nets, in turn delivering GC-free memory management with deterministic lifetimes. The key is that the compiler statically analyzes variable usage patterns to infer linear types, automatically inserting duplication and erasure operations that correspond to precise allocation and deallocation points.

The Interaction Net foundation also enables automatic parallelism, since independent subgraphs can reduce concurrently without synchronization overhead. The compiler offers three execution modes allowing developers to choose the appropriate performance-predictability tradeoff for their use case.

In practice, this means developers write composable functional code while the compiler guarantees systems-level performance: deterministic memory reclamation, predictable execution timing, and no runtime garbage collection overhead.

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

Or for projects:

```
haoma new <project-name>
cd <project-name>
haoma run -m <mode>
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

2. **Circuit IR 🔄**: An Interaction Net-based intermediate representation that achieves optimal (Lamping-style) evaluation without garbage collection.

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

1-3. **Same as Standard** (Metal → Circuit → Linearization)

4. **Graph Lowering 🕸️**: Linearized Circuit IR is lowered to Alloy's graph operations. The compiler knows statically where duplication occurs and can specialize: primitives use direct operations, complex types use the interaction net runtime.

5-7. **Same as Standard** (Alloy → LTO → LLVM)

**Runtime**: `inets_soma.a` - Interaction net runtime with compile-time duplication placement and work-stealing reduction. Achieves up to **8.77x speedup** (4 workers) on recursive workloads via automatic parallelism. Enable with `SOMA_WORKERS=N`.

### Key Benefits of Circuit IR

- **No GC pauses**: Memory is freed deterministically at consumption points (Standard/Hybrid)
- **Optimal sharing**: Interaction net reduction avoids recomputation (Graph mode)
- **Compile-time specialization**: Type-based optimization eliminates overhead for primitives (Graph mode)
- **Automatic parallelism**: Independent subgraphs reduce in parallel without locks (Graph mode)
- **Predictable performance**: No unpredictable collection pauses, real-time safe (all modes)
- **User choice**: Pick the right tradeoff between predictability (Standard), optional parallelism (Hybrid), or automatic parallelism (Graph)

---

# ✨ Etymology

Soma draws its name from three linguistic roots that together capture the language's philosophy:

1. **Portuguese: "soma" (sum/addition):** In mathematics, Σ denotes summation: the composition of many terms into a whole. Soma embraces this compositional spirit: monads chain effects, functions composition, and type classes let you abstract over structure. The syntax reads like notation, letting you build programs as elegant equations where complex behavior emerges from the sum of simple, pure parts.

2. **Sanskrit: सोम (soma):** In Vedic tradition, soma was a ritual drink prepared through extensive refinement: pressed, filtered, and purified. The name evokes transformation through process: taking raw materials and distilling them into something potent and essential. Soma the language shares this emphasis on refinement, where high-level abstractions are transformed into efficient machine code without losing their essential clarity.

3. **Greek: σῶμα (sôma) (body/substance):** In Greek philosophy, sôma represents the physical embodiment of form: the material instantiation of abstract ideas. Soma gives your functional abstractions a tangible body: the compiler translates pure, high-level code into concrete, efficient executables. Just as sôma grounds the ethereal in the corporeal, Soma grounds elegant code in performant machine behavior.

---

# 🙏 Acknowledgments

First and foremost, I would like to thank Jesus Christ for His guidance and blessings throughout this project and giving me the opportunity to create this.

Special thanks to **HigherOrderCo** (HOC) and **Victor Taelin** for their groundbreaking research and development in Interaction Nets and Interaction Calculus. Their work on optimal evaluation, the HVM runtime, and the theoretical foundations of interaction-based computation has been instrumental in developing Soma's Circuit IR and runtime system.

Lastly, thanks to the open-soruce community and researchers whose contributions made this project possible.
