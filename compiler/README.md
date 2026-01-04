# 📐 Soma Compiler: Lean4 Rewrite

This is a complete rewrite of the Soma compiler in Lean4, testing the waters by gradually migrating from the original Haskell implementation.

## What This Rewrite Achieves

1. **Comprehensive documentation from the start**  
   The original Haskell codebase was largely undocumented since I hadn't expected the project to grow this large. This rewrite documents everything from day one.

2. **Proven correctness of core invariants**  
   Linearization produces affine terms, type inference is sound, and critical passes preserve semantics, all verified by the type system.

3. **Elimination of defensive code**  
   No more runtime validation, no boolean phase flags, no "this should never happen" error branches. Illegal states are simply unrepresentable (which is tiring to achieve with GADTs or Liquid Haskell).

4. **Confidence in refactoring**  
   For example, if I ever change the linearization algorithm, the proof must still hold. If it compiles, the invariants are preserved.

5. **Improved maintainability**  
   Cleaner, more idiomatic code that replaces legacy hacks with proper implementations.
  
6. **Tests:**
    Previous code didn't have a lot of tests because they were written retroactively. This rewrite includes tests from the beginning.
