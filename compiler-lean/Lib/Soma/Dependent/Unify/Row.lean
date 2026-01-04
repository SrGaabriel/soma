import Soma.Core.Value
import Soma.Dependent.Monad
import Soma.Dependent.Unify.Core

namespace Soma.Dependent

open Soma.Core

/-- Find a label in a row and split it out -/
partial def splitRowAt (label : String) (row : Value) : TCM (Option (Value × Value)) := do
  match row with
  | .vRowEmpty => return none
  | .vRowExtend (.vLabelLit l) ty tail =>
    if l == label then
      return some (ty, tail)
    else
      match ← splitRowAt label tail with
      | some (foundTy, restTail) =>
        -- Reconstruct: { l : ty | restTail }
        return some (foundTy, .vRowExtend (.vLabelLit l) ty restTail)
      | none => return none
  | .vNeutral _ (.nMeta _) =>
    -- Row ends in a metavariable, can't split
    return none
  | _ => return none

end Soma.Dependent
