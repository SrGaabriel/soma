import Soma.Core.Value
import Soma.Dependent.Monad
import Soma.Dependent.Unify.Core

namespace Soma.Dependent

open Soma.Core

/-- Whether `v` a bare bound-variable neutral at the given level -/
def isBareBoundVarAt (v : Value) (lvl : DeBruijnLvl) : Bool :=
  match v with
  | .vNeutral _ (.mk (.hVar bv) spine) =>
    spine.isEmpty && bv.level.lvl == lvl.lvl
  | _ => false

/-- Find the position of `bv.level` in the captured spine -/
def findCapturedPosition (bvLevel : DeBruijnLvl) (captureSpine : List Value)
    : Option Nat :=
  let rec go (idx : Nat) : List Value → Option Nat
    | [] => none
    | v :: rest =>
      match v with
      | .vNeutral _ (.mk (.hVar bv) spine) =>
        if spine.isEmpty && bv.level.lvl == bvLevel.lvl then some idx
        else go (idx + 1) rest
      | _ =>
        none
  go 0 captureSpine

/-- The set of levels carried by the captured spine, in order -/
def captureLevels? (captureSpine : List Value) : Option (Array DeBruijnLvl) :=
  let rec go (acc : Array DeBruijnLvl) : List Value → Option (Array DeBruijnLvl)
    | [] => some acc
    | v :: rest =>
      match v with
      | .vNeutral _ (.mk (.hVar bv) spine) =>
        if spine.isEmpty then go (acc.push bv.level) rest
        else none
      | _ => none
  go #[] captureSpine

/-- Whether `v` mentions any free bound variable whose level isn't in `captureLevels` -/
def valueEscapesCaptures (v : Value) (captureLevels : Array DeBruijnLvl) : Bool :=
  let used := Soma.Dependent.collectFreeVars v
  used.any fun lvl => ! captureLevels.any (·.lvl == lvl.lvl)

/-- Variant of `valueEscapesCaptures` that takes the captured spine directly -/
def valueEscapesCapturedSpine (v : Value) (captureSpine : List Value) : Bool :=
  match captureLevels? captureSpine with
  | none => true
  | some lvls => valueEscapesCaptures v lvls

/-- Assert that an `InstanceInfo` is internally consistent against its declared `ClassInfo` -/
def instanceInfoWellFormedAgainst (inst : InstanceInfo) (classInfo : ClassInfo)
    : Bool :=
  inst.args.size == classInfo.numParams

/-- Assert + describe variant of `instanceInfoWellFormedAgainst` -/
def diagnoseInstanceInfo (inst : InstanceInfo) (classInfo : ClassInfo)
    : Option String :=
  if instanceInfoWellFormedAgainst inst classInfo then none
  else some s!"InstanceInfo arity mismatch: \
    class `{classInfo.classId.original}` declares \
    {classInfo.numParams} parameter(s) but instance was registered \
    with {inst.args.size} argument(s)"

end Soma.Dependent
