import Somac.Alloy.Func
import Std.Data.HashMap
import Std.Data.HashSet

namespace Somac.Alloy.ArithAccum

open Somac.Alloy

/-- An associative binary operation with its identity element -/
structure AssocOp where
  op : BinOp
  /-- The identity element for this operation -/
  identity : Int
  /-- Whether the operation is commutative -/
  commutative : Bool

/-- Known associative operations and their identity elements -/
private def assocOps : Array AssocOp := #[
  { op := .add, identity := 0, commutative := true },
  { op := .mul, identity := 1, commutative := true },
  { op := .or,  identity := 0, commutative := true },
  { op := .xor, identity := 0, commutative := true },
  { op := .and, identity := -1, commutative := true }
]

/-- Look up the associative info for a BinOp -/
private def findAssocOp (op : BinOp) : Option AssocOp :=
  assocOps.find? (·.op == op)

/-- Check whether a constant is the identity element for an associative op -/
private def isIdentity (c : Const) (info : AssocOp) : Bool :=
  match c with
  | .int val _ => val == info.identity
  | _ => false

/-- A detected arithmetic-after-self-call site -/
structure ArithRecSite where
  /-- Block containing the pattern -/
  blockId : Nat
  /-- Index of the self-call statement -/
  selfCallIdx : Nat
  /-- Result of the self-call -/
  selfCallResult : LocalId
  /-- Arguments to the self-call -/
  selfCallArgs : Array Operand
  /-- Index of the binOp statement -/
  binOpIdx : Nat
  /-- Result of the binOp -/
  binOpResult : LocalId
  /-- The associative operation -/
  op : BinOp
  /-- The non-recursive operand of the binOp -/
  stepOperand : Operand
  /-- The type of the binOp result -/
  resultTy : ClosedTy
  /-- Optional trampoline block between recursive block and exit -/
  trampolineBlockId : Option Nat
  /-- Exit block that merges base and recursive results via phi -/
  exitBlockId : Option Nat
  deriving Repr

/-- Find arithmetic-after-self-call patterns in a function -/
private def findArithRecSites (func : ClosedFunc) : Array ArithRecSite := Id.run do
  let some cfg := func.body | return #[]
  let selfId := func.id
  let mut sites : Array ArithRecSite := #[]

  let exitBlocks : Std.HashSet Nat := Id.run do
    let mut exits : Std.HashSet Nat := {}
    for (bid, block) in cfg.blocks.toArray do
      match block.terminator with
      | .ret _ | .retUnit => exits := exits.insert bid
      | _ => pure ()
    exits

  for (bid, block) in cfg.blocks.toArray do
    let mut selfCallInfo : Option (Nat × LocalId × Array Operand) := none

    for i in [:block.stmts.size] do
      let stmt := block.stmts[i]!
      match stmt.inst, stmt.result with
      | .call funcId args _, some resultId =>
        if funcId == selfId then
          selfCallInfo := some (i, resultId, args)
      | .binOp op lhs rhs ty, some resultId =>
        if let some info := findAssocOp op then
          if let some (scIdx, scResult, scArgs) := selfCallInfo then
            -- Check if one operand is the self-call result and the other is the "step"
            let match? :=
              match lhs, rhs with
              | .local lid, step =>
                if lid == scResult then some step else
                if info.commutative then
                  match step with
                  | .local rid => if rid == scResult then some lhs else none
                  | _ => none
                else none
              | step, .local rid =>
                if rid == scResult then some step else
                if info.commutative then
                  match step with
                  | .local lid => if lid == scResult then some rhs else none
                  | _ => none
                else none
              | _, _ => none
            if let some stepOp := match? then
              let resolveExit : Option (Option Nat × Option Nat) := Id.run do
                match block.terminator with
                | .ret (.local retId) =>
                  if retId == resultId then return some (none, none)
                | .jump target =>
                  -- Direct: target is an exit block with a phi referencing resultId
                  if exitBlocks.contains target.id then
                    if let some exitBlock := cfg.blocks.get? target.id then
                      let phiRefs := exitBlock.stmts.any fun s =>
                        match s.inst with
                        | .phi incoming _ =>
                          incoming.any fun (op, fromBlock) =>
                            fromBlock.id == bid && match op with
                              | .local lid => lid == resultId
                              | _ => false
                        | _ => false
                      if phiRefs then return some (none, some target.id)
                  -- Trampoline: target is an intermediate block with phi + jump to exit
                  if let some midBlock := cfg.blocks.get? target.id then
                    let midPhiResult := midBlock.stmts.findSome? fun s =>
                      match s.inst, s.result with
                      | .phi incoming _, some phiRes =>
                        let refs := incoming.any fun (op, fromBlock) =>
                          fromBlock.id == bid && match op with
                            | .local lid => lid == resultId
                            | _ => false
                        if refs then some phiRes else none
                      | _, _ => none
                    if let some midPhiRes := midPhiResult then
                      match midBlock.terminator with
                      | .jump exitTarget =>
                        if exitBlocks.contains exitTarget.id then
                          if let some exitBlock := cfg.blocks.get? exitTarget.id then
                            let exitPhiRefs := exitBlock.stmts.any fun s =>
                              match s.inst with
                              | .phi incoming _ =>
                                incoming.any fun (op, fromBlock) =>
                                  fromBlock.id == target.id && match op with
                                    | .local lid => lid == midPhiRes
                                    | _ => false
                              | _ => false
                            if exitPhiRefs then return some (some target.id, some exitTarget.id)
                      | _ => pure ()
                | _ => pure ()
                none
              if let some (trampolineId, exitBlockId) := resolveExit then
                sites := sites.push {
                  blockId := bid, selfCallIdx := scIdx,
                  selfCallResult := scResult, selfCallArgs := scArgs,
                  binOpIdx := i, binOpResult := resultId,
                  op := op, stepOperand := stepOp, resultTy := ty,
                  trampolineBlockId := trampolineId, exitBlockId := exitBlockId
                }
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

/-- Transform a function with arithmetic-after-self-call into accumulator-passing style -/
def transformFunc (func : ClosedFunc) : Option (ClosedFunc × Nat) := Id.run do
  let sites := findArithRecSites func
  if sites.isEmpty then return none
  let some cfg := func.body | return none
  let some site := sites[0]? | return none
  let some assocInfo := findAssocOp site.op | return none

  -- Allocate fresh locals
  let mut nextLocal := func.nextLocalId

  -- Accumulator slot and load
  let accSlotId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
  let accLoadId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1

  -- Parameter slots and loads
  let mut paramSlots : Array LocalId := #[]
  let mut paramLoads : Array LocalId := #[]
  let mut paramRemap : Std.HashMap Nat LocalId := {}
  let mut loopLocalTypes := func.localTypes

  for param in func.sig.params do
    let slotId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
    let loadId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
    paramSlots := paramSlots.push slotId
    paramLoads := paramLoads.push loadId
    paramRemap := paramRemap.insert param.id.id loadId
    loopLocalTypes := loopLocalTypes.insert slotId.id (.ptr param.ty)
    loopLocalTypes := loopLocalTypes.insert loadId.id param.ty

  loopLocalTypes := loopLocalTypes.insert accSlotId.id (.ptr site.resultTy)
  loopLocalTypes := loopLocalTypes.insert accLoadId.id site.resultTy

  let (loopBlockId, cfg) := cfg.freshBlockId

  let siteBlockIds : Std.HashSet Nat := sites.foldl (init := {}) fun acc s => acc.insert s.blockId

  -- Determine the PrimTy for the accumulator's identity constant
  let accPrimTy : PrimTy := match site.resultTy with
    | .prim p => p
    | _ => .i32

  let identityConst : Operand := .const (.int assocInfo.identity accPrimTy)

  -- Build entry block: alloca slots for params + accumulator, store initial values
  let mut entryStmts : Array ClosedStmt := #[]

  for i in [:func.sig.params.size] do
    let param := func.sig.params[i]!
    entryStmts := entryStmts.push { result := some paramSlots[i]!, inst := .alloca param.ty }
    entryStmts := entryStmts.push { result := none, inst := .store (.local paramSlots[i]!) (.local param.id) }

  entryStmts := entryStmts.push { result := some accSlotId, inst := .alloca site.resultTy }
  entryStmts := entryStmts.push { result := none, inst := .store (.local accSlotId) identityConst }

  let entryBlock : ClosedBlock := {
    id := cfg.entry, stmts := entryStmts, terminator := .jump loopBlockId
  }

  -- Build loop header: load params + acc, then original entry block body (remapped)
  let some origEntry := cfg.blocks.get? cfg.entry.id | return none
  let mut loopStmts : Array ClosedStmt := #[]

  for i in [:func.sig.params.size] do
    let param := func.sig.params[i]!
    loopStmts := loopStmts.push { result := some paramLoads[i]!, inst := .load (.local paramSlots[i]!) param.ty }

  loopStmts := loopStmts.push { result := some accLoadId, inst := .load (.local accSlotId) site.resultTy }
  loopStmts := loopStmts ++ origEntry.stmts.map (remapStmt · paramRemap)

  let loopBlock : ClosedBlock := {
    id := loopBlockId, label := some "arith_accum",
    stmts := loopStmts, terminator := remapTerminator origEntry.terminator paramRemap
  }

  -- Rewrite all blocks
  let mut newBlocks : Std.HashMap Nat ClosedBlock := {}
  newBlocks := newBlocks.insert cfg.entry.id entryBlock
  newBlocks := newBlocks.insert loopBlockId.id loopBlock

  for (bid, block) in cfg.blocks.toArray do
    if bid == cfg.entry.id then continue
    let mut newStmts := block.stmts.map (remapStmt · paramRemap)
    let mut newTerm := remapTerminator block.terminator paramRemap

    if let some site := sites.find? (fun s => s.blockId == bid) then
      let mut replacementStmts : Array ClosedStmt := #[]
      for i in [:newStmts.size] do
        if i == site.selfCallIdx || i == site.binOpIdx then continue
        replacementStmts := replacementStmts.push newStmts[i]!

      let newAccId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
      loopLocalTypes := loopLocalTypes.insert newAccId.id site.resultTy
      replacementStmts := replacementStmts.push {
        result := some newAccId,
        inst := .binOp site.op (.local accLoadId) (remapOperand site.stepOperand paramRemap) site.resultTy
      }
      replacementStmts := replacementStmts.push {
        result := none, inst := .store (.local accSlotId) (.local newAccId)
      }

      for i in [:func.sig.params.size] do
        if h : i < site.selfCallArgs.size then
          replacementStmts := replacementStmts.push {
            result := none, inst := .store (.local paramSlots[i]!) (remapOperand site.selfCallArgs[i] paramRemap)
          }

      newStmts := replacementStmts
      newTerm := .jump loopBlockId

    -- Patch phis: entry→loop, remove recursive-site edges
    newStmts := newStmts.map fun stmt =>
      match stmt.inst with
      | .phi incoming ty =>
        let patched := incoming.filterMap fun (op, fromBlock) =>
          if siteBlockIds.contains fromBlock.id then none
          else if fromBlock.id == cfg.entry.id then some (op, loopBlockId)
          else some (op, fromBlock)
        { stmt with inst := .phi patched ty }
      | _ => stmt

    let isExitBlock := sites.any fun s => s.exitBlockId == some bid
    if isExitBlock then
      -- Find the phi's result id (the base case value, now dominating in this block)
      let mut phiResultId : Option LocalId := none
      let mut phiIsConstIdentity := false
      for stmt in newStmts do
        match stmt.inst, stmt.result with
        | .phi incoming _, some rid =>
          phiResultId := some rid
          -- Check if all remaining incoming values are identity constants
          phiIsConstIdentity := incoming.all fun (op, _) =>
            match op with
            | .const c => isIdentity c assocInfo
            | _ => false
        | _, _ => pure ()

      -- Load final accumulator value (append after existing stmts including the phi)
      let accFinalId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
      loopLocalTypes := loopLocalTypes.insert accFinalId.id site.resultTy
      newStmts := newStmts.push {
        result := some accFinalId, inst := .load (.local accSlotId) site.resultTy
      }

      -- If base is identity, return acc directly; otherwise acc ⊕ base
      let mut retId := accFinalId
      if let some phiRes := phiResultId then
        if !phiIsConstIdentity then
          let combinedId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
          loopLocalTypes := loopLocalTypes.insert combinedId.id site.resultTy
          newStmts := newStmts.push {
            result := some combinedId,
            inst := .binOp site.op (.local accFinalId) (.local phiRes) site.resultTy
          }
          retId := combinedId

      newTerm := .ret (.local retId)

    newBlocks := newBlocks.insert bid { block with stmts := newStmts, terminator := newTerm }

  let newCfg : ClosedCFG := { cfg with blocks := newBlocks }
  some ({ func with
    body := some newCfg,
    nextLocalId := nextLocal,
    localTypes := loopLocalTypes
  }, sites.size)

/-- Apply arithmetic accumulator introduction to all functions in a module -/
def arithAccumIntro (m : Module) : Module × Nat := Id.run do
  let mut newFuncs : Array SomeFunc := #[]
  let mut totalConverted : Nat := 0

  for sf in m.funcs do
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

  ({ m with funcs := newFuncs }, totalConverted)

end Somac.Alloy.ArithAccum
