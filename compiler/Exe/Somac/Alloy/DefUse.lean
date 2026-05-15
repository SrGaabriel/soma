import Somac.Alloy.Func
import Std.Data.HashMap
import Std.Data.HashSet

namespace Somac.Alloy.DefUse

open Somac.Alloy

/-- Location of a statement within a CFG -/
structure StmtLoc where
  blockId : Nat
  stmtIdx : Nat
  deriving BEq, Hashable, Repr, Inhabited

/-- Precomputed use-def and liveness information for a function -/
structure DefUseInfo where
  /-- Where each local is defined: LocalId.id → StmtLoc -/
  defSite : Std.HashMap Nat StmtLoc
  /-- All use sites for each local: LocalId.id → Array StmtLoc -/
  uses : Std.HashMap Nat (Array StmtLoc)
  /-- Locals that are live at the entry of each block: BlockId → HashSet LocalId.id -/
  liveIn : Std.HashMap Nat (Std.HashSet Nat)
  /-- Locals that are live at the exit of each block: BlockId → HashSet LocalId.id -/
  liveOut : Std.HashMap Nat (Std.HashSet Nat)
  deriving Inhabited

/-- Compute DefUseInfo for a closed function -/
def analyze (f : ClosedFunc) : DefUseInfo := Id.run do
  let some cfg := f.body |
    return { defSite := {}, uses := {}, liveIn := {}, liveOut := {} }

  let mut defSite : Std.HashMap Nat StmtLoc := {}
  let mut uses : Std.HashMap Nat (Array StmtLoc) := {}

  let addUse := fun (uses : Std.HashMap Nat (Array StmtLoc)) (lid : Nat) (loc : StmtLoc) =>
    let arr := uses.getD lid #[]
    uses.insert lid (arr.push loc)

  for block in cfg.allBlocks do
    let bid := block.id.id
    for h : i in [:block.stmts.size] do
      let stmt := block.stmts[i]
      let loc : StmtLoc := { blockId := bid, stmtIdx := i }

      if let some rid := stmt.result then
        defSite := defSite.insert rid.id loc

      for lid in stmt.inst.localUses do
        uses := addUse uses lid.id loc

    -- Terminator uses (sentinel stmtIdx = stmts.size)
    let termLoc : StmtLoc := { blockId := bid, stmtIdx := block.stmts.size }
    for lid in block.terminator.localUses do
      uses := addUse uses lid.id termLoc

  -- Precompute upward-exposed uses and defs per block
  let mut blockUse : Std.HashMap Nat (Std.HashSet Nat) := {}
  let mut blockDef : Std.HashMap Nat (Std.HashSet Nat) := {}

  for block in cfg.allBlocks do
    let bid := block.id.id
    let mut useSet : Std.HashSet Nat := {}
    let mut defSet : Std.HashSet Nat := {}

    for stmt in block.stmts do
      for lid in stmt.inst.localUses do
        if !defSet.contains lid.id then
          useSet := useSet.insert lid.id
      if let some rid := stmt.result then
        defSet := defSet.insert rid.id

    for lid in block.terminator.localUses do
      if !defSet.contains lid.id then
        useSet := useSet.insert lid.id

    blockUse := blockUse.insert bid useSet
    blockDef := blockDef.insert bid defSet

  -- Successor map
  let mut succMap : Std.HashMap Nat (Array Nat) := {}
  for block in cfg.allBlocks do
    succMap := succMap.insert block.id.id (block.successors.map (·.id))

  -- Fixpoint iteration
  let rpo := cfg.reversePostorder
  let mut liveIn : Std.HashMap Nat (Std.HashSet Nat) := {}
  let mut liveOut : Std.HashMap Nat (Std.HashSet Nat) := {}

  for _ in [:30] do
    let mut changed := false

    -- Process in reverse RPO (successors before predecessors for backward analysis)
    for bidIdx in [:rpo.size] do
      let bid := rpo[rpo.size - 1 - bidIdx]!
      let bidId := bid.id

      let mut newLiveOut : Std.HashSet Nat := {}
      for succId in succMap.getD bidId #[] do
        for lid in liveIn.getD succId {} do
          newLiveOut := newLiveOut.insert lid

      let defB := blockDef.getD bidId {}
      let mut newLiveIn : Std.HashSet Nat := {}
      for lid in blockUse.getD bidId {} do
        newLiveIn := newLiveIn.insert lid
      for lid in newLiveOut do
        if !defB.contains lid then
          newLiveIn := newLiveIn.insert lid

      let prevIn := liveIn.getD bidId {}
      let prevOut := liveOut.getD bidId {}
      if newLiveIn.size != prevIn.size || newLiveOut.size != prevOut.size then
        changed := true

      liveIn := liveIn.insert bidId newLiveIn
      liveOut := liveOut.insert bidId newLiveOut

    if !changed then break

  return { defSite, uses, liveIn, liveOut }

end Somac.Alloy.DefUse
