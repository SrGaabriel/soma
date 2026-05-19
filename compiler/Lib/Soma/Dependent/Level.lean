import Soma.Core.Level
import Soma.Dependent.Monad
import Soma.Dependent.Error
import Soma.Dependent.Convert

namespace Soma.Dependent

open Soma.Core

/-- Apply current solutions to a level -/
partial def applyLevelSolutions (solutions : Std.HashMap Nat Level) (l : Level) : Level :=
  match l with
  | .prop => .prop
  | .lit n => .lit n
  | .var v =>
    match solutions.get? v.id with
    | some l' => applyLevelSolutions solutions l'
    | none => .var v
  | .max l1 l2 =>
    Level.mkMax (applyLevelSolutions solutions l1) (applyLevelSolutions solutions l2)
  | .succ l' =>
    Level.mkSucc (applyLevelSolutions solutions l')

/-- Apply level solutions to a level -/
def solveLevelVars (l : Level) : TCM Level := do
  let state ← TCM.getState
  let solutions := state.levelSolutions
  return applyLevelSolutions solutions l

/-- Apply level solutions to a Value -/
partial def zonkValueLevels (v : Value) : TCM Value := do
  match v with
  | .vType l =>
    let l' ← solveLevelVars l
    return .vType l'
  | .vPi qty binder name dom cod =>
    let dom' ← zonkValueLevels dom
    -- Closures contain terms, not values with levels, so skip
    return .vPi qty binder name dom' cod
  | .vLam name dom body =>
    let dom' ← zonkValueLevels dom
    return .vLam name dom' body
  | .vNeutral ty neu =>
    let ty' ← zonkValueLevels ty
    return .vNeutral ty' neu
  | .vRecord row =>
    let row' ← zonkValueLevels row
    return .vRecord row'
  | .vVariant row =>
    let row' ← zonkValueLevels row
    return .vVariant row'
  | .vRowExtend label fieldTy tail =>
    let label' ← zonkValueLevels label
    let fieldTy' ← zonkValueLevels fieldTy
    let tail' ← zonkValueLevels tail
    return .vRowExtend label' fieldTy' tail'
  | .vDataType id params =>
    let params' ← params.mapM zonkValueLevels
    return .vDataType id params'
  | .vConstructor name tag args rty =>
    let args' ← args.mapM zonkValueLevels
    let rty' ← zonkValueLevels rty
    return .vConstructor name tag args' rty'
  -- Values without levels
  | .vIntLit _ | .vFloatLit _ | .vStringLit _
  | .vRowEmpty | .vLabelLit _ | .vRecordVal _
  | .vRowSort | .vLabelSort =>
    return v

end Soma.Dependent
