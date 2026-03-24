import Somac.Alloy.Func
import Std.Data.HashMap
import Std.Data.HashSet

namespace Somac.Alloy.ElemSize

open Somac.Alloy

private def isListExtern (name : String) : Bool :=
  name == "soma_list_cons" || name == "soma_list_head" ||
  name == "soma_list_tail" || name == "soma_list_dup"

/-- Determine the list element size for a function by analyzing its instructions -/
private def inferElemSize (func : ClosedFunc) (ptrBytes : Nat) : Option Nat := Id.run do
  let some cfg := func.body | return none

  let mut headResults : Std.HashSet Nat := {}
  let mut allocaTypes : Std.HashMap Nat ClosedTy := {}

  for (_, block) in cfg.blocks.toArray do
    for stmt in block.stmts do
      match stmt.inst, stmt.result with
      | .alloca ty, some rid => allocaTypes := allocaTypes.insert rid.id ty
      | .callExtern "soma_list_head" _ _, some rid => headResults := headResults.insert rid.id
      | _, _ => pure ()

  -- Strategy 1: load from head result → element type
  for (_, block) in cfg.blocks.toArray do
    for stmt in block.stmts do
      match stmt.inst with
      | .load (.local ptr) ty =>
        if headResults.contains ptr.id then
          let sz := ty.sizeBytes ptrBytes
          if sz > 0 then return some sz
      | _ => pure ()

  -- Strategy 2: alloca passed as first arg to soma_list_cons → element type
  for (_, block) in cfg.blocks.toArray do
    for stmt in block.stmts do
      match stmt.inst with
      | .callExtern "soma_list_cons" args _ =>
        if args.size >= 1 then
          match args[0]! with
          | .local lid =>
            if let some ty := allocaTypes.get? lid.id then
              let sz := ty.sizeBytes ptrBytes
              if sz > 0 then return some sz
          | _ => pure ()
      | _ => pure ()

  none

/-- Rewrite all `elem_size` arguments in `soma_list_*` calls in a function body -/
private def rewriteElemSizes (func : ClosedFunc) (newElemSize : Nat) (ptrBytes : Nat)
    : ClosedFunc := Id.run do
  let some cfg := func.body | return func
  if newElemSize == ptrBytes then return func  -- no change needed

  let oldElemSize := ptrBytes

  -- Find the LocalId(s) holding the old elem_size constant
  let mut elemSizeLocals : Std.HashSet Nat := {}
  for (_, block) in cfg.blocks.toArray do
    for stmt in block.stmts do
      match stmt.inst, stmt.result with
      | .copy (.const (.int val .u16)), some rid =>
        if val == Int.ofNat oldElemSize then
          elemSizeLocals := elemSizeLocals.insert rid.id
      | _, _ => pure ()

  if elemSizeLocals.isEmpty then return func

  -- Create a new constant for the correct elem_size
  let mut newBlocks := cfg.blocks
  for (bid, block) in cfg.blocks.toArray do
    let mut changed := false
    let mut newStmts := block.stmts
    for i in [:block.stmts.size] do
      let stmt := block.stmts[i]!
      match stmt.inst, stmt.result with
      | .copy (.const (.int val .u16)), some rid =>
        if val == Int.ofNat oldElemSize && elemSizeLocals.contains rid.id then
          -- Check that this local is actually used in a soma_list_* call
          let usedInListCall := block.stmts.any fun s =>
            match s.inst with
            | .callExtern name args _ =>
              isListExtern name && args.any fun a => match a with
                | .local lid => lid == rid
                | _ => false
            | _ => false
          if usedInListCall then
            newStmts := newStmts.set! i
              { stmt with inst := .copy (.const (.int (Int.ofNat newElemSize) .u16)) }
            changed := true
      | _, _ => pure ()
    if changed then
      newBlocks := newBlocks.insert bid { block with stmts := newStmts }

  { func with body := some { cfg with blocks := newBlocks } }

/-- Apply element size refinement to all monomorphized functions in a module -/
def refineElemSizes (m : Module) (ptrBytes : Nat) : Module × Nat := Id.run do
  let mut newFuncs : Array SomeFunc := #[]
  let mut refined : Nat := 0

  for sf in m.funcs do
    match sf.asMono? with
    | some f =>
      match inferElemSize f ptrBytes with
      | some elemSz =>
        if elemSz != ptrBytes then
          newFuncs := newFuncs.push (SomeFunc.ofMono (rewriteElemSizes f elemSz ptrBytes))
          refined := refined + 1
        else
          newFuncs := newFuncs.push sf
      | none =>
        newFuncs := newFuncs.push sf
    | none =>
      newFuncs := newFuncs.push sf

  ({ m with funcs := newFuncs }, refined)

end Somac.Alloy.ElemSize
