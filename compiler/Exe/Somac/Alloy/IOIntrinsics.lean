import Somac.Alloy.Func
import Std.Data.HashMap

namespace Somac.Alloy.IOIntrinsics

open Somac.Alloy

/-- Check if a function is a wired-in `pure_io` -/
private def isPureIOFunc (f : ClosedFunc) : Bool :=
  f.attrs.wiredRole == some .pureIO && f.sig.params.size >= 1

/-- Check if a function is a wired-in `io_bind` -/
private def isBindIOFunc (f : ClosedFunc) : Bool :=
  f.attrs.wiredRole == some .bindIO && f.sig.params.size >= 2

/-- Build the pure_io body: identity function returning parameter 0 -/
private def buildPureIOBody (f : ClosedFunc) : ClosedFunc :=
  let paramId := f.sig.params[0]!.id
  let entryBlockId : BlockId := ⟨0⟩
  let block : ClosedBlock := {
    id := entryBlockId,
    stmts := #[],
    terminator := .ret (.local paramId)
  }
  let cfg : ClosedCFG := {
    entry := entryBlockId,
    blocks := ({} : Std.HashMap Nat ClosedBlock).insert entryBlockId.id block
  }
  { f with body := some cfg }

/-- Build the io_bind body -/
private def buildBindIOBody (f : ClosedFunc) : ClosedFunc := Id.run do
  let mParam := f.sig.params[0]!
  let fParam := f.sig.params[1]!
  let retTy := f.sig.retTy

  let entryBlockId : BlockId := ⟨0⟩
  let mut nextLocal := f.nextLocalId
  let mut stmts : Array ClosedStmt := #[]
  let mut localTypes := f.localTypes

  -- If m is a closure (IO thunk), call it with unit to force evaluation
  let (aVal, nextLocal', stmts', localTypes') ← match mParam.ty with
    | .closure _ mRetTy =>
      let unitId : LocalId := ⟨nextLocal⟩
      let aId : LocalId := ⟨nextLocal + 1⟩
      let s := stmts
        |>.push { result := some unitId, inst := .copy (.const .unit) }
        |>.push { result := some aId, inst := .callClosure (.local mParam.id) #[.local unitId] mRetTy }
      let lt := localTypes
        |>.insert unitId.id (.prim .unit)
        |>.insert aId.id mRetTy
      pure (aId, nextLocal + 2, s, lt)
    | _ =>
      pure (mParam.id, nextLocal, stmts, localTypes)

  nextLocal := nextLocal'
  stmts := stmts'
  localTypes := localTypes'

  -- Call f with the 'a' value to get the continuation result
  let fResultTy := match fParam.ty with
    | .closure _ ret => ret
    | _ => retTy
  let fResultId : LocalId := ⟨nextLocal⟩
  nextLocal := nextLocal + 1
  stmts := stmts.push { result := some fResultId, inst := .callClosure (.local fParam.id) #[.local aVal] fResultTy }
  localTypes := localTypes.insert fResultId.id fResultTy

  -- If f returned a closure (IO thunk), call it with unit to force
  let (bVal, nextLocal', stmts', localTypes') ← match fResultTy with
    | .closure _ innerRetTy =>
      let unitId : LocalId := ⟨nextLocal⟩
      let bId : LocalId := ⟨nextLocal + 1⟩
      let s := stmts
        |>.push { result := some unitId, inst := .copy (.const .unit) }
        |>.push { result := some bId, inst := .callClosure (.local fResultId) #[.local unitId] innerRetTy }
      let lt := localTypes
        |>.insert unitId.id (.prim .unit)
        |>.insert bId.id innerRetTy
      pure (bId, nextLocal + 2, s, lt)
    | _ =>
      pure (fResultId, nextLocal, stmts, localTypes)

  nextLocal := nextLocal'
  stmts := stmts'
  localTypes := localTypes'

  -- Handle the case where the final value type doesn't match retTy
  let finalVal := bVal

  let block : ClosedBlock := {
    id := entryBlockId,
    stmts := stmts,
    terminator := if retTy == .prim .unit then .retUnit else .ret (.local finalVal)
  }
  let cfg : ClosedCFG := {
    entry := entryBlockId,
    blocks := ({} : Std.HashMap Nat ClosedBlock).insert entryBlockId.id block
  }
  { f with body := some cfg, nextLocalId := nextLocal, localTypes := localTypes }

/-- Replace io_bind and pure_io bodies with erasure-correct intrinsic implementations -/
def replaceIOIntrinsics (m : Module) : Module × Nat := Id.run do
  let mut newFuncs : Array SomeFunc := #[]
  let mut replaced : Nat := 0

  for sf in m.funcs do
    match sf.asMono? with
    | some f =>
      if isPureIOFunc f then
        newFuncs := newFuncs.push (SomeFunc.ofMono (buildPureIOBody f))
        replaced := replaced + 1
      else if isBindIOFunc f then
        newFuncs := newFuncs.push (SomeFunc.ofMono (buildBindIOBody f))
        replaced := replaced + 1
      else
        newFuncs := newFuncs.push sf
    | none =>
      newFuncs := newFuncs.push sf

  ({ m with funcs := newFuncs }, replaced)

end Somac.Alloy.IOIntrinsics
