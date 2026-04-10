import Somac.Alloy.Func
import Std.Data.HashMap
import Std.Data.HashSet

namespace Somac.Alloy.TailCall

open Somac.Alloy

/-- A detected tail-call site -/
structure TailCallSite where
  blockId : Nat
  callStmtIdx : Nat
  callResultId : LocalId
  callArgs : Array Operand
  exitBlockId : Option Nat
  deriving Repr

/-- Find all self-recursive tail-call sites in a function -/
private def findTailCalls (func : ClosedFunc) (selfId : FuncId) : Array TailCallSite := Id.run do
  let some cfg := func.body | return #[]
  let mut sites : Array TailCallSite := #[]

  let exitBlocks : Std.HashSet Nat := Id.run do
    let mut exits : Std.HashSet Nat := {}
    for (bid, block) in cfg.blocks.toArray do
      match block.terminator with
      | .ret _ | .retUnit => exits := exits.insert bid
      | _ => pure ()
    exits

  for (bid, block) in cfg.blocks.toArray do
    let mut lastResultIdx : Option Nat := none
    for i in [:block.stmts.size] do
      if block.stmts[i]!.result.isSome then
        lastResultIdx := some i

    match lastResultIdx with
    | none => pure ()
    | some idx =>
      let stmt := block.stmts[idx]!
      match stmt.inst, stmt.result with
      | .call funcId args _, some resultId =>
        if funcId == selfId then
          match block.terminator with
          | .jump target =>
            if exitBlocks.contains target.id then
              if let some exitBlock := cfg.blocks.get? target.id then
                let phiRefsResult := exitBlock.stmts.any fun s =>
                  match s.inst with
                  | .phi incoming _ =>
                    incoming.any fun (op, fromBlock) =>
                      fromBlock.id == bid && match op with
                        | .local lid => lid == resultId
                        | _ => false
                  | _ => false
                if phiRefsResult then
                  sites := sites.push {
                    blockId := bid, callStmtIdx := idx,
                    callResultId := resultId, callArgs := args,
                    exitBlockId := some target.id
                  }
          | .ret (.local retId) =>
            if retId == resultId then
              sites := sites.push {
                blockId := bid, callStmtIdx := idx,
                callResultId := resultId, callArgs := args,
                exitBlockId := none
              }
          | _ => pure ()
      | _, _ => pure ()
  sites

/-- Rewrite an operand using a parameter remapping -/
private def remapOperand (op : Operand) (remap : Std.HashMap Nat LocalId) : Operand :=
  match op with
  | .local lid => match remap.get? lid.id with
    | some newId => .local newId
    | none => op
  | _ => op

/-- Rewrite all operands in a statement -/
private def remapStmt (stmt : ClosedStmt) (remap : Std.HashMap Nat LocalId) : ClosedStmt :=
  { stmt with inst := stmt.inst.mapOperands (remapOperand · remap) }

/-- Rewrite all operands in a terminator -/
private def remapTerminator (term : Terminator) (remap : Std.HashMap Nat LocalId) : Terminator :=
  term.mapOperands (remapOperand · remap)

/-- Convert a closed type to its pointer-wrapped form for alloca -/
private def slotTy (ty : ClosedTy) : ClosedTy := .ptr ty

/-- Transform a function with self-recursive tail calls into a loop -/
def transformFunc (func : ClosedFunc) : Option (ClosedFunc × Nat) := Id.run do
  let some cfg := func.body | return none
  let sites := findTailCalls func func.id
  if sites.isEmpty then return none

  let (loopBlockId, cfg) := cfg.freshBlockId

  -- Allocate fresh locals for: stack slots, loaded loop variables
  let mut nextLocal := func.nextLocalId
  let mut slotIds : Array LocalId := #[]
  let mut loadIds : Array LocalId := #[]
  let mut paramRemap : Std.HashMap Nat LocalId := {}
  let mut loopLocalTypes := func.localTypes

  for param in func.sig.params do
    let slotId : LocalId := ⟨nextLocal⟩
    nextLocal := nextLocal + 1
    let loadId : LocalId := ⟨nextLocal⟩
    nextLocal := nextLocal + 1
    slotIds := slotIds.push slotId
    loadIds := loadIds.push loadId
    paramRemap := paramRemap.insert param.id.id loadId
    loopLocalTypes := loopLocalTypes.insert slotId.id (slotTy param.ty)
    loopLocalTypes := loopLocalTypes.insert loadId.id param.ty

  let tailCallBlockIds : Std.HashSet Nat := sites.foldl (init := {}) fun acc s => acc.insert s.blockId

  -- Build entry block: alloca slots + store initial param values + jump to loop
  let mut entryStmts : Array ClosedStmt := #[]
  for i in [:func.sig.params.size] do
    let param := func.sig.params[i]!
    -- %slot_i = alloca param_ty
    entryStmts := entryStmts.push {
      result := some slotIds[i]!,
      inst := .alloca param.ty
    }
    -- store %param_i, %slot_i
    entryStmts := entryStmts.push {
      result := none,
      inst := .store (.local slotIds[i]!) (.local param.id)
    }

  let entryBlock : ClosedBlock := {
    id := cfg.entry,
    stmts := entryStmts,
    terminator := .jump loopBlockId
  }

  -- Build loop header: load from slots + original entry block body (remapped)
  let some origEntry := cfg.blocks.get? cfg.entry.id | return none
  let mut loopStmts : Array ClosedStmt := #[]

  for i in [:func.sig.params.size] do
    let param := func.sig.params[i]!
    -- %load_i = load %slot_i
    loopStmts := loopStmts.push {
      result := some loadIds[i]!,
      inst := .load (.local slotIds[i]!) param.ty
    }

  -- Append original entry stmts with params remapped to loaded values
  loopStmts := loopStmts ++ origEntry.stmts.map (remapStmt · paramRemap)

  let loopBlock : ClosedBlock := {
    id := loopBlockId,
    label := some "loop",
    stmts := loopStmts,
    terminator := remapTerminator origEntry.terminator paramRemap
  }

  -- Rewrite all other blocks
  let mut newBlocks : Std.HashMap Nat ClosedBlock := {}
  newBlocks := newBlocks.insert cfg.entry.id entryBlock
  newBlocks := newBlocks.insert loopBlockId.id loopBlock

  for (bid, block) in cfg.blocks.toArray do
    if bid == cfg.entry.id then continue
    let mut newStmts := block.stmts.map (remapStmt · paramRemap)
    let mut newTerm := remapTerminator block.terminator paramRemap

    -- Tail-call block: replace call with stores to slots + jump to loop
    if let some site := sites.find? (fun s => s.blockId == bid) then
      -- Remove the self-call statement
      newStmts := newStmts.eraseIdx! site.callStmtIdx
      -- Store new args into slots
      let mut storeStmts : Array ClosedStmt := #[]
      for i in [:func.sig.params.size] do
        if h : i < site.callArgs.size then
          let arg := remapOperand site.callArgs[i] paramRemap
          storeStmts := storeStmts.push {
            result := none,
            inst := .store (.local slotIds[i]!) arg
          }
      newStmts := newStmts ++ storeStmts
      newTerm := .jump loopBlockId

    -- Patch phi incoming edges
    newStmts := newStmts.map fun stmt =>
      match stmt.inst with
      | .phi incoming ty =>
        let patched := incoming.filterMap fun (op, fromBlock) =>
          if tailCallBlockIds.contains fromBlock.id then
            none
          else if fromBlock.id == cfg.entry.id then
            some (op, loopBlockId)
          else
            some (op, fromBlock)
        { stmt with inst := .phi patched ty }
      | _ => stmt

    newBlocks := newBlocks.insert bid { block with stmts := newStmts, terminator := newTerm }

  let newCfg : ClosedCFG := { cfg with blocks := newBlocks }
  let newFunc := { func with
    body := some newCfg,
    nextLocalId := nextLocal,
    localTypes := loopLocalTypes
  }
  some (newFunc, sites.size)

/-- Apply tail call optimization to all functions in a module -/
def tailCallOpt (m : Module) : Module × Nat := Id.run do
  let mut module := m
  let mut totalConverted : Nat := 0
  let mut newFuncs : Array SomeFunc := #[]

  for sf in module.funcs do
    match sf.asMono? with
    | some f =>
      match transformFunc f with
      | some (optimized, count) =>
        newFuncs := newFuncs.push (SomeFunc.ofMono optimized)
        totalConverted := totalConverted + count
      | none =>
        newFuncs := newFuncs.push sf
    | none =>
      newFuncs := newFuncs.push sf

  ({ module with funcs := newFuncs }, totalConverted)

/-- A cross-function tail call site -/
structure MutualTailCallSite where
  funcId : FuncId
  calleeFuncId : FuncId
  blockId : Nat
  callStmtIdx : Nat
  callResultId : LocalId
  callArgs : Array Operand
  exitBlockId : Option Nat

/-- Find cross-function tail calls in a function (to any function in `allFuncIds`, excluding self) -/
private def findMutualTailCalls (func : ClosedFunc) (allFuncIds : Std.HashSet Nat)
    : Array MutualTailCallSite := Id.run do
  let some cfg := func.body | return #[]
  let mut sites : Array MutualTailCallSite := #[]

  let exitBlocks : Std.HashSet Nat := Id.run do
    let mut exits : Std.HashSet Nat := {}
    for (bid, block) in cfg.blocks.toArray do
      match block.terminator with
      | .ret _ | .retUnit => exits := exits.insert bid
      | _ => pure ()
    exits

  for (bid, block) in cfg.blocks.toArray do
    let mut lastResultIdx : Option Nat := none
    for i in [:block.stmts.size] do
      if block.stmts[i]!.result.isSome then
        lastResultIdx := some i
    match lastResultIdx with
    | none => pure ()
    | some idx =>
      let stmt := block.stmts[idx]!
      match stmt.inst, stmt.result with
      | .call funcId args callRetTy, some resultId =>
        -- Cross-function only (self-calls already handled by TCO pass)
        if funcId != func.id && allFuncIds.contains funcId.id
           && callRetTy == func.sig.retTy then
          match block.terminator with
          | .jump target =>
            if exitBlocks.contains target.id then
              if let some exitBlock := cfg.blocks.get? target.id then
                let phiRefsResult := exitBlock.stmts.any fun s =>
                  match s.inst with
                  | .phi incoming _ =>
                    incoming.any fun (op, fromBlock) =>
                      fromBlock.id == bid && match op with
                        | .local lid => lid == resultId
                        | _ => false
                  | _ => false
                if phiRefsResult then
                  sites := sites.push {
                    funcId := func.id, calleeFuncId := funcId,
                    blockId := bid, callStmtIdx := idx,
                    callResultId := resultId, callArgs := args,
                    exitBlockId := some target.id
                  }
          | .ret (.local retId) =>
            if retId == resultId then
              sites := sites.push {
                funcId := func.id, calleeFuncId := funcId,
                blockId := bid, callStmtIdx := idx,
                callResultId := resultId, callArgs := args,
                exitBlockId := none
              }
          | _ => pure ()
      | _, _ => pure ()
  sites

/-- Transform cross-function tail calls to use direct `ret` (enabling musttail) -/
private def transformMutualTailCalls (func : ClosedFunc) (sites : Array MutualTailCallSite)
    : ClosedFunc := Id.run do
  let some cfg := func.body | return func
  let mut newBlocks := cfg.blocks

  for site in sites do
    if let some block := newBlocks.get? site.blockId then
      let newTerm := Terminator.ret (.local site.callResultId)
      newBlocks := newBlocks.insert site.blockId { block with terminator := newTerm }

      if let some exitBid := site.exitBlockId then
        if let some exitBlock := newBlocks.get? exitBid then
          let newExitStmts := exitBlock.stmts.map fun stmt =>
            match stmt.inst with
            | .phi incoming ty =>
              let filtered := incoming.filter fun (_, fromBlock) => fromBlock.id != site.blockId
              { stmt with inst := .phi filtered ty }
            | _ => stmt
          newBlocks := newBlocks.insert exitBid { exitBlock with stmts := newExitStmts }

  let newCfg := { cfg with blocks := newBlocks }
  { func with body := some newCfg }

/-- Apply mutual tail call optimization to a module -/
def mutualTailCallOpt (m : Module) : Module × Nat := Id.run do
  let allFuncIds : Std.HashSet Nat := m.funcs.foldl (init := {}) fun acc sf =>
    match sf.asMono? with
    | some f => acc.insert f.id.id
    | none => acc

  let mut newFuncs : Array SomeFunc := #[]
  let mut totalConverted : Nat := 0

  for sf in m.funcs do
    match sf.asMono? with
    | some f =>
      let sites := findMutualTailCalls f allFuncIds
      if sites.isEmpty then
        newFuncs := newFuncs.push sf
      else
        let optimized := transformMutualTailCalls f sites
        newFuncs := newFuncs.push (SomeFunc.ofMono optimized)
        totalConverted := totalConverted + sites.size
    | none =>
      newFuncs := newFuncs.push sf

  ({ m with funcs := newFuncs }, totalConverted)

end Somac.Alloy.TailCall
