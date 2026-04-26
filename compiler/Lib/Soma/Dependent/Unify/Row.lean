import Soma.Core.Value
import Soma.Dependent.Monad
import Soma.Dependent.Unify.Core

namespace Soma.Dependent

open Soma.Core

/-- Find a label in a row and split it out -/
partial def splitRowAt (label : String) (row : Value) : TCM (Option (Value × Value)) := do
  let row ← force row
  match row with
  | .vRowEmpty => return none
  | .vRowExtend (.vLabelLit l) ty tail =>
    if l == label then
      return some (ty, tail)
    else
      match ← splitRowAt label tail with
      | some (foundTy, restTail) =>
        return some (foundTy, .vRowExtend (.vLabelLit l) ty restTail)
      | none => return none
  | _ => return none

/-- Find a label in a row -/
partial def splitRowAtExtending (label : String) (row : Value)
    : TCM (Option (Value × Value)) := do
  let row ← force row
  match row with
  | .vRowEmpty => return none
  | .vRowExtend (.vLabelLit l) ty tail =>
    if l == label then
      return some (ty, tail)
    else
      match ← splitRowAtExtending label tail with
      | some (foundTy, restTail) =>
        return some (foundTy, .vRowExtend (.vLabelLit l) ty restTail)
      | none => return none
  | .vNeutral _ (.nMeta m) =>
    let newTy ← TCM.freshMetaVal (.vType .zero)
    let newTail ← TCM.freshMetaVal .vRowSort
    let extension := Value.vRowExtend (.vLabelLit label) newTy newTail
    TCM.solveMeta m extension
    return some (newTy, newTail)
  | _ => return none

end Soma.Dependent
