import Somac.Alloy.Func
import Std.Data.HashMap
import Std.Data.HashSet

namespace Somac.Alloy.AccumIntro

open Somac.Alloy

/-- Information about a detected cons-after-self-call pattern -/
structure ConsRecSite where
  /-- Block containing the pattern -/
  blockId : Nat
  /-- Index of the self-call statement -/
  selfCallIdx : Nat
  /-- Result of the self-call -/
  selfCallResult : LocalId
  /-- Arguments to the self-call -/
  selfCallArgs : Array Operand
  /-- Index of the soma_list_cons call -/
  consCallIdx : Nat
  /-- Result of the cons call -/
  consResult : LocalId
  /-- The element operand passed to cons -/
  consElemOp : Operand
  /-- The element size operand -/
  consSizeOp : Operand
  /-- Exit block -/
  exitBlockId : Nat
  deriving Repr

/-- Look up a wired-in 2-param list reverse function (reverse_onto / reverse_acc) -/
private def findReverseFunc (m : Module) (retTy : ClosedTy) : Option FuncId := Id.run do
  let some candidates := m.wiredFuncIds.get? .listReverse | return none
  for fid in candidates do
    if let some f := m.getMonoFunc fid then
      if f.sig.params.size == 2 && f.sig.retTy == retTy then
        return some fid
  none

/-- Check if an instruction is a call to soma_list_cons -/
private def isListCons (inst : ClosedInst) : Bool :=
  match inst with
  | .callExtern name _ _ => name == "soma_list_cons"
  | _ => false

/-- Detect cons-after-self-call pattern in a function -/
private def findConsRecSites (func : ClosedFunc) : Array ConsRecSite := Id.run do
  let some cfg := func.body | return #[]
  let selfId := func.id
  let mut sites : Array ConsRecSite := #[]

  let exitBlocks : Std.HashSet Nat := Id.run do
    let mut exits : Std.HashSet Nat := {}
    for (bid, block) in cfg.blocks.toArray do
      match block.terminator with
      | .ret _ | .retUnit => exits := exits.insert bid
      | _ => pure ()
    exits

  for (bid, block) in cfg.blocks.toArray do
    let mut selfCallInfo : Option (Nat × LocalId × Array Operand) := none
    let mut consCallInfo : Option (Nat × LocalId × Operand × Operand) := none

    for i in [:block.stmts.size] do
      let stmt := block.stmts[i]!
      match stmt.inst, stmt.result with
      | .call funcId args _, some resultId =>
        if funcId == selfId then
          selfCallInfo := some (i, resultId, args)
      | .callExtern name args _, some resultId =>
        if name == "soma_list_cons" && args.size >= 3 then
          -- Check if the second arg (tail) is the self-call result
          match selfCallInfo with
          | some (_, selfResultId, _) =>
            match args[1]! with
            | .local lid =>
              if lid == selfResultId then
                consCallInfo := some (i, resultId, args[0]!, args[2]!)
            | _ => pure ()
          | none => pure ()
      | _, _ => pure ()

    -- Verify: cons result flows to exit via phi
    match selfCallInfo, consCallInfo with
    | some (scIdx, scResult, scArgs), some (ccIdx, ccResult, elemOp, sizeOp) =>
      match block.terminator with
      | .jump target =>
        if exitBlocks.contains target.id then
          sites := sites.push {
            blockId := bid, selfCallIdx := scIdx,
            selfCallResult := scResult, selfCallArgs := scArgs,
            consCallIdx := ccIdx, consResult := ccResult,
            consElemOp := elemOp, consSizeOp := sizeOp,
            exitBlockId := target.id
          }
      | _ => pure ()
    | _, _ => pure ()

  sites

/-- Transform a function with cons-after-self-call into accumulator-passing style -/
def transformFunc (m : Module) (func : ClosedFunc) : Option (ClosedFunc × Nat) := Id.run do
  let sites := findConsRecSites func
  if sites.isEmpty then return none

  -- Need a wired-in reverse function to finalize the accumulated list
  let some reverseAccId := findReverseFunc m func.sig.retTy | return none
  let some cfg := func.body | return none
  let listTy : ClosedTy := Ty.somaList

  -- We handle functions with exactly one list parameter that is recursed on
  let some site := sites[0]? | return none

  -- Allocate fresh locals
  let mut nextLocal := func.nextLocalId
  let accSlotId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
  let accLoadId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
  let reversedId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1

  -- Also need slots for all function params (for the loop, same as TCO)
  let mut paramSlots : Array LocalId := #[]
  let mut paramLoads : Array LocalId := #[]
  let mut paramRemap : Std.HashMap Nat LocalId := {}

  for param in func.sig.params do
    let slotId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
    let loadId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
    paramSlots := paramSlots.push slotId
    paramLoads := paramLoads.push loadId
    paramRemap := paramRemap.insert param.id.id loadId

  let (loopBlockId, cfg) := cfg.freshBlockId

  -- Remap helper
  let remapOp := fun (op : Operand) =>
    match op with
    | .local lid => match paramRemap.get? lid.id with
      | some newId => .local newId
      | none => op
    | _ => op

  let remapStmtFn := fun (stmt : ClosedStmt) =>
    { stmt with inst := stmt.inst.mapOperands remapOp }

  let remapTermFn := fun (term : Terminator) =>
    term.mapOperands remapOp

  let siteBlockIds : Std.HashSet Nat := sites.foldl (init := {}) fun acc s => acc.insert s.blockId

  -- Build entry block: alloca slots for params + accumulator, store initial values
  let mut entryStmts : Array ClosedStmt := #[]

  -- Param slots
  for i in [:func.sig.params.size] do
    let param := func.sig.params[i]!
    entryStmts := entryStmts.push { result := some paramSlots[i]!, inst := .alloca param.ty }
    entryStmts := entryStmts.push { result := none, inst := .store (.local paramSlots[i]!) (.local param.id) }

  -- Accumulator slot (initially Nil = { null, 0, 0, 0 })
  let nilId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
  let nilLitInst : ClosedInst := .structLit
    #[.const (.null .rawPtr), .const (.int 0 .u32), .const (.int 0 .u32)] listTy
  entryStmts := entryStmts.push { result := some accSlotId, inst := .alloca listTy }
  entryStmts := entryStmts.push { result := some nilId, inst := nilLitInst }
  entryStmts := entryStmts.push { result := none, inst := .store (.local accSlotId) (.local nilId) }

  let entryBlock : ClosedBlock := {
    id := cfg.entry, stmts := entryStmts, terminator := .jump loopBlockId
  }

  -- Build loop header: load params + acc from slots, then original entry body
  let some origEntry := cfg.blocks.get? cfg.entry.id | return none
  let mut loopStmts : Array ClosedStmt := #[]

  for i in [:func.sig.params.size] do
    let param := func.sig.params[i]!
    loopStmts := loopStmts.push { result := some paramLoads[i]!, inst := .load (.local paramSlots[i]!) param.ty }

  -- Acc load (used in cons sites)
  loopStmts := loopStmts.push { result := some accLoadId, inst := .load (.local accSlotId) listTy }

  loopStmts := loopStmts ++ origEntry.stmts.map remapStmtFn

  let loopBlock : ClosedBlock := {
    id := loopBlockId, label := some "accum_loop",
    stmts := loopStmts, terminator := remapTermFn origEntry.terminator
  }

  -- Rewrite all blocks
  let mut newBlocks : Std.HashMap Nat ClosedBlock := {}
  newBlocks := newBlocks.insert cfg.entry.id entryBlock
  newBlocks := newBlocks.insert loopBlockId.id loopBlock

  for (bid, block) in cfg.blocks.toArray do
    if bid == cfg.entry.id then continue
    let mut newStmts := block.stmts.map remapStmtFn
    let mut newTerm := remapTermFn block.terminator

    if let some site := sites.find? (fun s => s.blockId == bid) then
      -- Build replacement statements: keep everything EXCEPT self-call and cons
      let mut replacementStmts : Array ClosedStmt := #[]
      for i in [:newStmts.size] do
        if i == site.selfCallIdx || i == site.consCallIdx then continue
        replacementStmts := replacementStmts.push newStmts[i]!

      let newAccId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
      replacementStmts := replacementStmts.push {
        result := some newAccId,
        inst := .callExtern "soma_list_cons" #[remapOp site.consElemOp, .local accLoadId, remapOp site.consSizeOp] listTy
      }
      replacementStmts := replacementStmts.push {
        result := none, inst := .store (.local accSlotId) (.local newAccId)
      }
      for i in [:func.sig.params.size] do
        if h : i < site.selfCallArgs.size then
          replacementStmts := replacementStmts.push {
            result := none, inst := .store (.local paramSlots[i]!) (remapOp site.selfCallArgs[i])
          }

      newStmts := replacementStmts
      newTerm := .jump loopBlockId

    -- Patch phis: entry→loop, remove cons-site edges
    newStmts := newStmts.map fun stmt =>
      match stmt.inst with
      | .phi incoming ty =>
        let patched := incoming.filterMap fun (op, fromBlock) =>
          if siteBlockIds.contains fromBlock.id then none
          else if fromBlock.id == cfg.entry.id then some (op, loopBlockId)
          else some (op, fromBlock)
        { stmt with inst := .phi patched ty }
      | _ => stmt

    -- If this is an exit block that previously merged cons results,
    -- replace: phi → ret with: load acc, reverse_acc(acc, base_value), ret
    let isExitBlock := sites.any fun s => s.exitBlockId == bid
    if isExitBlock then
      -- Extract the base-case value from the phi's remaining (non-cons-site) edges.
      let mut baseValue : Operand := .const (.null .rawPtr)
      for stmt in newStmts do
        match stmt.inst with
        | .phi incoming _ =>
          if let some (val, _) := incoming[0]? then
            baseValue := val
        | _ => pure ()

      -- Remove phi, add: load acc → reverse_acc(acc, base_value) → ret
      let mut finalStmts : Array ClosedStmt := #[]
      for stmt in newStmts do
        match stmt.inst with
        | .phi _ _ => pure ()
        | _ => finalStmts := finalStmts.push stmt

      let accFinalId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
      finalStmts := finalStmts.push {
        result := some accFinalId, inst := .load (.local accSlotId) listTy
      }
      finalStmts := finalStmts.push {
        result := some reversedId,
        inst := .call reverseAccId #[.local accFinalId, baseValue] listTy
      }
      newStmts := finalStmts
      newTerm := .ret (.local reversedId)

    newBlocks := newBlocks.insert bid { block with stmts := newStmts, terminator := newTerm }

  let mut newLocalTypes := func.localTypes
  newLocalTypes := newLocalTypes.insert accSlotId.id (.ptr listTy)
  newLocalTypes := newLocalTypes.insert accLoadId.id listTy
  newLocalTypes := newLocalTypes.insert reversedId.id listTy
  newLocalTypes := newLocalTypes.insert nilId.id listTy
  for i in [:func.sig.params.size] do
    let param := func.sig.params[i]!
    newLocalTypes := newLocalTypes.insert paramSlots[i]!.id (.ptr param.ty)
    newLocalTypes := newLocalTypes.insert paramLoads[i]!.id param.ty

  let newCfg : ClosedCFG := { cfg with blocks := newBlocks }
  some ({ func with body := some newCfg, nextLocalId := nextLocal, localTypes := newLocalTypes }, sites.size)

/-- Apply accumulator introduction to all functions in a module -/
def accumIntro (m : Module) : Module × Nat := Id.run do
  let mut module := m
  let mut totalConverted : Nat := 0
  let mut newFuncs : Array SomeFunc := #[]

  for sf in module.funcs do
    match sf.asMono? with
    | some f =>
      match transformFunc module f with
      | some (optimized, count) =>
        newFuncs := newFuncs.push (SomeFunc.ofMono optimized)
        totalConverted := totalConverted + count
      | none =>
        newFuncs := newFuncs.push sf
    | none =>
      newFuncs := newFuncs.push sf

  ({ module with funcs := newFuncs }, totalConverted)

end Somac.Alloy.AccumIntro
