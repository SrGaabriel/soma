/-
  Alloy IR: Mid-level Intermediate Representation for Soma

  Alloy is an imperative, SSA-based IR positioned between Circuit IR and LLVM IR.
  It serves as the primary compilation target after interaction net lowering.

  Pipeline:
    Metal IR → Circuit IR → **Alloy IR** → LLVM IR → Native Code

  Key features:
  - SSA form with explicit phi nodes
  - Explicit memory operations (alloca, malloc, load, store)
  - Explicit control flow (basic blocks with terminators)
  - Closures as struct + function pointer pairs
  - No interaction net concepts (DUP/SUP resolved to explicit operations)
-/

import Soma.Alloy.Types
import Soma.Alloy.Inst
import Soma.Alloy.Block
import Soma.Alloy.Func
import Soma.Alloy.Lower
import Soma.Alloy.Pretty

namespace Soma.Alloy

-- All types are already exported by their respective modules in Soma.Alloy namespace
-- Re-export lowering and pretty printing functions

export Lower (lower lowerGraph)
export Pretty (pp ppColored ppFn ppBb ppModule)

end Soma.Alloy
