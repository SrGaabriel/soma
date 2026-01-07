![GitHub branch status](https://img.shields.io/github/checks-status/SrGaabriel/soma/main?style=for-the-badge)
![GitHub Repo stars](https://img.shields.io/github/stars/SrGaabriel/soma?style=for-the-badge)
![GitHub License](https://img.shields.io/github/license/SrGaabriel/soma?style=for-the-badge)


# ⚗️ soma

Soma is a statically-typed, pure functional language with the [Calculus of Quantitative Constructions (CQC)](docs/CQC.md) for dependent types, explicit effect modeling, and eager evaluation semantics. It leverages Interaction Nets for optimal evaluation, enabling GC-free memory management with deterministic lifetimes, zero-cost proofs, and automatic parallelism.

---

## ✨ Overview

Combining high-level expressiveness with predictable performance characteristics, Soma features the [Calculus of Quantitative Constructions (CQC)](docs/CQC.md), a dependent type system with quantities that track variable usage (erased, linear, or unrestricted). The language supports eager evaluation semantics, explicit effect modeling, and System F-ω typing to enable aggressive optimization.

Soma achieves optimal evaluation via Interaction Nets, in turn delivering GC-free memory management with deterministic lifetimes. The key is that the compiler statically analyzes variable usage patterns through quantities, automatically inserting duplication and erasure operations that correspond to precise allocation and deallocation points.

The Interaction Net foundation also enables automatic parallelism, since independent subgraphs can reduce concurrently without synchronization overhead. The compiler offers three execution modes allowing developers to choose the appropriate performance-predictability tradeoff for their use case.

In practice, this means developers write composable functional code with optional dependent types for compile-time guarantees (vector lengths, protocol states, resource usage) while the compiler guarantees systems-level performance: deterministic memory reclamation, predictable execution timing, zero-cost proofs, and no runtime garbage collection overhead.

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

# ✨ Etymology

Soma draws its name from three linguistic roots that together capture the language's philosophy:

1. **Portuguese: "soma" (sum/addition):** In mathematics, Σ denotes summation: the composition of many terms into a whole. Soma embraces this compositional spirit: monads chain effects, functions composition, and type classes let you abstract over structure. The syntax reads like notation, letting you build programs as elegant equations where complex behavior emerges from the sum of simple, pure parts.

2. **Sanskrit: सोम (soma):** In Vedic tradition, soma was a ritual drink prepared through extensive refinement: pressed, filtered, and purified. The name evokes transformation through process: taking raw materials and distilling them into something potent and essential. Soma the language shares this emphasis on refinement, where high-level abstractions are transformed into efficient machine code without losing their essential clarity.

3. **Greek: σῶμα (sôma) (body/substance):** In Greek philosophy, sôma represents the physical embodiment of form: the material instantiation of abstract ideas. Soma gives your functional abstractions a tangible body: the compiler translates pure, high-level code into concrete, efficient executables. Just as sôma grounds the ethereal in the corporeal, Soma grounds elegant code in performant machine behavior.

---

# 🙏 Acknowledgments

First and foremost, I would like to thank Jesus Christ for His guidance and blessings throughout this project and giving me the opportunity to create this.

Special thanks to **HigherOrderCo** (HOC) and **Victor Taelin** for their groundbreaking research and development in Interaction Nets and Interaction Calculus. Their work on optimal evaluation, the HVM runtime, and the theoretical foundations of interaction-based computation has been instrumental in developing Soma's Circuit IR and runtime system.

Lastly, thanks to the open-source community and researchers whose contributions made this project possible.
