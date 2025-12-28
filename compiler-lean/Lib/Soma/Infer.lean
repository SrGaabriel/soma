/-
  Soma Type Inference

  This module provides Hindley-Milner type inference with:
  - Constraint-based inference (Algorithm W style)
  - Type class support with instance resolution
  - Kind-indexed types for safety
  - Span-based error reporting

  Key improvements over the old Haskell implementation:
  1. Span-based errors (no "magic spans" workaround)
  2. Constraint graph structure for efficient lookup
  3. Instance entailment checks BOTH class name AND type unification
  4. Uses real Metal types (no duplicated simplified types)
  5. Cleaner separation of concerns (no entangled resolver)

  Usage:
    let result := inferExpr expr context
    if result.isSuccess then
      -- use result.finalType
    else
      -- handle result.errors
-/

import Soma.Infer.Error
import Soma.Infer.Substitution
import Soma.Infer.Unify
import Soma.Infer.Constraint
import Soma.Infer.Instance
import Soma.Infer.Entailment
import Soma.Infer.Monad
import Soma.Infer.Gen
import Soma.Infer.Solver
import Soma.Infer.Module

namespace Soma.Infer

end Soma.Infer
