import Somac.Alloy.Func
import Std.Data.HashMap

namespace Somac.Alloy.ListIntrinsics

open Somac.Alloy

/-- Check if a function is a wired-in `length` -/
private def isLengthFunc (f : ClosedFunc) : Bool :=
  f.attrs.wiredRole == some .listLength &&
  f.sig.params.size == 1 &&
  f.sig.params[0]!.ty.isSomaList &&
  match f.sig.retTy with
  | .prim .i32 | .prim .i64 => true
  | _ => false

/-- Build a trivial length body: extract `len` field, truncate if needed, return -/
private def buildLengthBody (f : ClosedFunc) : ClosedFunc := Id.run do
  let paramId := f.sig.params[0]!.id
  let entryBlockId : BlockId := ⟨0⟩
  let mut nextLocal := f.nextLocalId
  let mut stmts : Array ClosedStmt := #[]
  let mut localTypes := f.localTypes

  -- %len = extractfield %param, 1  (the `len` field is u32)
  let lenId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
  stmts := stmts.push { result := some lenId, inst := .extractField (.local paramId) 1 }
  localTypes := localTypes.insert lenId.id (.prim .u32)

  -- len is u32; if return type is i32 (same width), use directly
  let retId ← match f.sig.retTy with
    | .prim .i32 =>
      pure lenId
    | .prim .i64 =>
      let extId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
      stmts := stmts.push { result := some extId, inst := .unOp (.zext .i64) (.local lenId) }
      localTypes := localTypes.insert extId.id (.prim .i64)
      pure extId
    | _ => pure lenId

  let block : ClosedBlock := {
    id := entryBlockId,
    stmts := stmts,
    terminator := .ret (.local retId)
  }

  let cfg : ClosedCFG := {
    entry := entryBlockId,
    blocks := ({} : Std.HashMap Nat ClosedBlock).insert entryBlockId.id block
  }

  { f with body := some cfg, nextLocalId := nextLocal, localTypes := localTypes }

/-- Apply list intrinsic replacements to a module -/
def replaceListIntrinsics (m : Module) : Module × Nat := Id.run do
  let mut newFuncs : Array SomeFunc := #[]
  let mut replaced : Nat := 0

  for sf in m.funcs do
    match sf.asMono? with
    | some f =>
      if isLengthFunc f then
        newFuncs := newFuncs.push (SomeFunc.ofMono (buildLengthBody f))
        replaced := replaced + 1
      else
        newFuncs := newFuncs.push sf
    | none =>
      newFuncs := newFuncs.push sf

  ({ m with funcs := newFuncs }, replaced)

end Somac.Alloy.ListIntrinsics
