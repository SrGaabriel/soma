/-
  CQC is **partial by default**: functions may not terminate, and that's fine
  for most programming. However, when a function is marked `@[total]`, we
  check that it terminates.

  ## Key Principles

  1. **Partial by Default**: No termination checking unless `@[total]` is used
  2. **Structural Recursion**: For `@[total]` functions, we check that recursive
     calls are on structurally smaller arguments
  3. **Type Index Restriction**: Only `@[total]` functions can appear in type indices
  4. **Positivity**: Always enforced for data types (prevents paradoxes)

  Inspired by: https://x.com/VictorTaelin/status/1997642824708215168
-/

import Soma.Dependent.Totality.Core
import Soma.Dependent.Totality.TermShape
import Soma.Dependent.Totality.CallMatrix
import Soma.Dependent.Totality.LPO
import Soma.Dependent.Totality.Positivity
import Soma.Dependent.Totality.Check

namespace Soma.Dependent.Totality

end Soma.Dependent.Totality
