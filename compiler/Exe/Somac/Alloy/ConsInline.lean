import Somac.Alloy.Func
import Std.Data.HashMap

namespace Somac.Alloy.ConsInline

open Somac.Alloy

private def inlineConsInFunc (func : ClosedFunc) : ClosedFunc := Id.run do
  let some cfg := func.body | return func
  let mut nextLocal := func.nextLocalId
  let mut nextBlockId := cfg.blocks.toArray.foldl (fun acc (k, _) => max acc (k + 1)) 1

  let mut consBlockIds : Array Nat := #[]
  for (bid, block) in cfg.blocks.toArray do
    let hasCons := block.stmts.any fun s =>
      match s.inst with
      | .callExtern "soma_list_cons" args retTy => args.size == 3 && retTy.isSomaList
      | _ => false
    if hasCons then consBlockIds := consBlockIds.push bid

  if consBlockIds.isEmpty then return func

  let mut allBlocks := cfg.blocks
  let mut remap : Std.HashMap Nat Nat := {}

  for bid in consBlockIds do
    let some block := allBlocks.get? bid | continue

    let mut preStmts : Array ClosedStmt := #[]
    let mut postStmts : Array ClosedStmt := #[]
    let mut foundCons : Option ClosedStmt := none

    for stmt in block.stmts do
      if foundCons.isNone then
        match stmt.inst, stmt.result with
        | .callExtern "soma_list_cons" args retTy, some _ =>
          if args.size == 3 && retTy.isSomaList then
            foundCons := some stmt
          else preStmts := preStmts.push stmt
        | _, _ => preStmts := preStmts.push stmt
      else
        postStmts := postStmts.push stmt

    let some cons := foundCons | continue
    let some resultId := cons.result | continue
    let .callExtern _ args _ := cons.inst | continue
    let elemOp := args[0]!
    let tailOp := args[1]!
    let elemSzOp := args[2]!

    -- Allocate fresh block IDs
    let preBid : BlockId := ⟨nextBlockId⟩; nextBlockId := nextBlockId + 1
    let fastBid : BlockId := ⟨nextBlockId⟩; nextBlockId := nextBlockId + 1
    let slowBid : BlockId := ⟨nextBlockId⟩; nextBlockId := nextBlockId + 1
    let joinBid : BlockId := ⟨bid⟩

    remap := remap.insert bid preBid.id

    -- Pre-block: original pre-stmts + offset check + branch
    let offsetId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
    let zeroId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
    let condId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
    preStmts := preStmts.push (Stmt.withResult offsetId (.extractField tailOp 2))
    preStmts := preStmts.push (Stmt.withResult zeroId (.copy (.const (.int 0 .u32))))
    preStmts := preStmts.push (Stmt.withResult condId
      (.binOp .ne (Operand.local offsetId) (Operand.local zeroId) (.prim .u32)))

    let preTerm : Terminator := .branch (Operand.local condId) fastBid slowBid
    allBlocks := allBlocks.insert preBid.id {
      id := preBid, label := block.label,
      stmts := preStmts,
      terminator := preTerm
    }

    -- Fast-path: inline prepend
    let mut fastStmts : Array ClosedStmt := #[]
    let dataId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
    let lenId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
    let oneId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
    let newOffId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
    let newLenId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
    let off64 : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
    let esz64 : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
    let byteOff : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
    let dstId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
    let fastResultId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
    let u32Ty : ClosedTy := .prim .u32
    let i64Ty : ClosedTy := .prim .i64
    let O := Operand.local
    fastStmts := fastStmts.push (Stmt.withResult dataId (.extractField tailOp 0))
    fastStmts := fastStmts.push (Stmt.withResult lenId (.extractField tailOp 1))
    fastStmts := fastStmts.push (Stmt.withResult oneId (.copy (.const (.int 1 .u32))))
    fastStmts := fastStmts.push (Stmt.withResult newOffId (.binOp .sub (O offsetId) (O oneId) u32Ty))
    fastStmts := fastStmts.push (Stmt.withResult newLenId (.binOp .add (O lenId) (O oneId) u32Ty))
    fastStmts := fastStmts.push (Stmt.withResult off64 (.unOp (.zext .i64) (O newOffId)))
    fastStmts := fastStmts.push (Stmt.withResult esz64 (.unOp (.zext .i64) elemSzOp))
    fastStmts := fastStmts.push (Stmt.withResult byteOff (.binOp .mul (O off64) (O esz64) i64Ty))
    fastStmts := fastStmts.push (Stmt.withResult dstId (.callIntrinsic .ptrAdd #[O dataId, O byteOff] .rawPtr))
    fastStmts := fastStmts.push (Stmt.void (.memcpy (O dstId) elemOp (O esz64)))
    fastStmts := fastStmts.push (Stmt.withResult fastResultId (.structLit #[O dataId, O newLenId, O newOffId] .somaList))

    allBlocks := allBlocks.insert fastBid.id {
      id := fastBid, label := some "cons_fast",
      stmts := fastStmts, terminator := .jump joinBid
    }

    -- Slow-path: runtime call
    let slowResultId : LocalId := ⟨nextLocal⟩; nextLocal := nextLocal + 1
    allBlocks := allBlocks.insert slowBid.id {
      id := slowBid, label := some "cons_slow",
      stmts := #[Stmt.withResult slowResultId cons.inst],
      terminator := .jump joinBid
    }

    -- Join block: cons phi + post stmts + original terminator (keeps original block ID)
    let consPhiIncoming : Array (Operand × BlockId) :=
      #[(Operand.local fastResultId, fastBid), (Operand.local slowResultId, slowBid)]
    let consPhi : ClosedStmt := {
      result := some resultId,
      inst := .phi consPhiIncoming .somaList
    }
    let mut joinStmts : Array ClosedStmt := #[consPhi]
    joinStmts := joinStmts ++ postStmts
    allBlocks := allBlocks.insert joinBid.id {
      id := joinBid,
      stmts := joinStmts, terminator := block.terminator
    }

  let remapId (bid : BlockId) : BlockId :=
    match remap.get? bid.id with
    | some newId => ⟨newId⟩
    | none => bid

  let mut finalBlocks : Std.HashMap Nat ClosedBlock := {}
  for (bid, block) in allBlocks.toArray do
    let isNewBlock := remap.any fun origId preId =>
      bid == preId || bid == origId
    let isConsHelperBlock := consBlockIds.any fun origId =>
      match remap.get? origId with
      | some preId => bid == preId + 1 || bid == preId + 2
      | none => false
    let newTerm := if isNewBlock || isConsHelperBlock then block.terminator
      else match block.terminator with
        | .jump t => .jump (remapId t)
        | .branch c t f => .branch c (remapId t) (remapId f)
        | other => other
    finalBlocks := finalBlocks.insert bid { block with terminator := newTerm }

  let newEntry := remapId cfg.entry

  { func with
    body := some { entry := newEntry, blocks := finalBlocks },
    nextLocalId := nextLocal }

/-- Apply cons fast-path inlining to all functions in a module -/
def inlineConsFastPath (m : Module) : Module × Nat := Id.run do
  let mut newFuncs : Array SomeFunc := #[]
  let mut count : Nat := 0

  for sf in m.funcs do
    match sf.asMono? with
    | some f =>
      let optimized := inlineConsInFunc f
      if optimized.nextLocalId != f.nextLocalId then
        count := count + 1
      newFuncs := newFuncs.push (SomeFunc.ofMono optimized)
    | none =>
      newFuncs := newFuncs.push sf

  ({ m with funcs := newFuncs }, count)

end Somac.Alloy.ConsInline
