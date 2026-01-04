# Test Strategy

This document describes the testing strategy for the compiler. The goal is to catch bugs early, prevent regressions, and ensure correctness across all compiler phases.

---

## Overview

The test suite is organized into several categories:

| Category | Purpose | Tools |
|----------|---------|-------|
| Unit Tests | Test individual functions/modules in isolation | HSpec |
| Integration Tests | Test the full compilation pipeline | HSpec + Golden |
| Property Tests | Verify invariants with random inputs | QuickCheck |
| Regression Tests | Prevent previously-fixed bugs from returning | HSpec + Golden |
| Validation Tests | Check IR structural invariants | HSpec |
| Benchmarks | Track compilation performance | Criterion |

---

## Directory Structure

```
test/
├── Spec.hs                        # Main test driver (hspec-discover)
├── Test/
│   ├── Generators.hs              # QuickCheck generators for IR types
│   └── Utils.hs                   # Shared test utilities
├── Unit/
│   ├── Lexing/
│   │   └── LexerSpec.hs
│   ├── Parsing/
│   │   └── ParserSpec.hs
│   ├── Inference/
│   │   ├── GenSpec.hs
│   │   ├── ResolverSpec.hs
│   │   └── SolvingSpec.hs
│   ├── Metal/
│   │   ├── LiftSpec.hs
│   │   └── NormalizeSpec.hs
│   ├── Circuit/
│   │   ├── LowerSpec.hs
│   │   └── LinearizeSpec.hs
│   └── Alloy/
│       ├── MonomorphizeSpec.hs
│       ├── DefuncSpec.hs
│       ├── InlineSpec.hs
│       └── SimplifySpec.hs
├── Integration/
│   ├── GoldenSpec.hs              # Snapshot tests for IR outputs
│   ├── E2ESpec.hs                 # Compile-and-run tests
│   └── RegressionSpec.hs          # Tests for fixed bugs
├── Property/
│   ├── LexerSpec.hs
│   ├── ParserSpec.hs
│   ├── InferenceSpec.hs
│   ├── LinearizationSpec.hs
│   └── AlloySpec.hs
├── Validation/
│   ├── CircuitSpec.hs
│   └── AlloySpec.hs
├── fixtures/                      # Small input files for unit tests
│   ├── valid.soma
│   ├── parse_error.soma
│   └── type_error.soma
├── golden/                        # Expected outputs for golden tests
│   ├── basic/
│   │   ├── identity.soma
│   │   ├── identity.metal.golden
│   │   ├── identity.circuit.golden
│   │   ├── identity.alloy.golden
│   │   └── identity.ll.golden
│   ├── patterns/
│   ├── closures/
│   └── traits/
└── regression/                    # Programs that triggered past bugs
    ├── issue_001_lambda_capture.soma
    └── ...

bench/
├── Bench.hs                       # Criterion benchmark suite
└── inputs/                        # Benchmark input files
```