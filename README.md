# 🚀 soma

Soma is a statically-typed, pure functional language with Hindley–Milner style type inference and a practical, performance-minded compiler.

---

## ✨ Overview

Soma aims to give you readable, expressive code while the compiler handles specialization and optimization up front. It is statically typed (Hindley–Milner), evaluates eagerly (so memory and CPU behavior are easier to predict), and models effects explicitly so the optimizer can treat most code as pure.

The compiler turns high-level functional pattern into efficient first-order code using lambda-lifting, specialization (monomorphization), and targeted inlining. The backend emits LLVM IR and performs link‑time style optimizations so the generated code can be comparable to optimized native implementations.

Put simply: write composable, declarative code; the compiler does the heavy lifting to make it run like systems code.

---

## 🛠️ Compiler backend breakdown

1. Metal (HIR) 🧱: After inference the compiler produces a higher-level IR. This stage performs lambda-lifting (so nested functions become explicit top-level closures) and normalization to get a predictable, analyzable shape.

2. Alloy (MIR) 🔁: Mid-level IR & transforms The HIR is lowered to a mid-level IR where the bulk of optimizations happen. This is where polymorphism is prepared for specialization, monadic patterns are normalized, and candidate optimizations are applied.

3. LTO ⚡: Separately-compiled modules are fused for whole-program passes. This LTO-style phase enables cross-module monomorphization, inlining, and aggressive specialization.

4. LLVM 🛡️: The optimized IR is translated to LLVM IR. From there you can use standard LLVM tools to produce object files or executables.

# ✨ Etymology
Soma draws its name from three linguistic roots that together capture the language's philosophy:

1. **Portuguese: "soma" (sum/addition):** In mathematics, Σ denotes summation: the composition of many terms into a whole. Soma embraces this compositional spirit: monads chain effects, functions composition, and type classes let you abstract over structure. The syntax reads like notation, letting you build programs as elegant equations where complex behavior emerges from the sum of simple, pure parts.

2. **Sanskrit: सोम (soma):** In Vedic tradition, soma was a sacred elixir extracted through precise, multi-stage refinement—pressed, filtered, distilled—transforming raw plant matter into concentrated divine essence. Soma the language performs an analogous transformation: your high-level functional abstractions passes through each stage refining and concentrating your code's computational power until what emerges is potent, optimized machine code that has shed all inefficiency while preserving its essential purity.

3. **Greek: σῶμα (sôma) (body/substance):** While you compose pure abstractions, Soma provides the material foundation that makes them real. The compiler handles the dirty work giving your ethereal functional code a solid, efficient body that runs on actual hardware.