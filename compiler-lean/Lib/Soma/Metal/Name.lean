/-
  Soma.Metal.Name - Re-exports Soma.Core.Name for backwards compatibility

  The naming infrastructure has been moved to Soma.Core.Name.
  This module re-exports everything for existing code that imports Soma.Metal.Name.
-/
import Soma.Core.Name

namespace Soma.Metal

-- Re-export all naming types from Core (open makes constructors available)
open Soma.Core (
  LocalPrefix
  LocalId
  BindingId
  RuntimeFn
  PrimOp
  Intrinsic
  DictKind
  DictId
  SyntheticKind
  Name
) in
export Soma.Core (
  LocalPrefix
  LocalId
  BindingId
  RuntimeFn
  PrimOp
  Intrinsic
  DictKind
  DictId
  SyntheticKind
  Name
)

end Soma.Metal
