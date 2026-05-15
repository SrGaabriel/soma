import Somac.Alloy.Func
import Std.Data.HashMap
import Std.Data.HashSet

namespace Somac.Alloy.Analysis

open Somac.Alloy

/-- An abstract value domain forming a join-semilattice -/
structure Domain (α : Type) where
  /-- Bottom element: no information (unreached path) -/
  bot : α
  /-- Join two abstract values at a control flow merge point -/
  join : α → α → α
  /-- Equality check for convergence detection -/
  eq : α → α → Bool

/-- Per-local abstract state: maps `LocalId.id → α` -/
structure AbsState (α : Type) where
  vals : Std.HashMap Nat α := {}
  deriving Inhabited

namespace AbsState

/-- Look up a local's abstract value, defaulting to `bot` -/
def get (d : Domain α) (s : AbsState α) (lid : Nat) : α :=
  s.vals.getD lid d.bot

/-- Set a local's abstract value -/
def set (s : AbsState α) (lid : Nat) (v : α) : AbsState α :=
  { vals := s.vals.insert lid v }

/-- Element-wise join of two states -/
def join (d : Domain α) (a b : AbsState α) : AbsState α :=
  let merged := a.vals.fold (init := b.vals) fun acc k v =>
    match acc.get? k with
    | some v' => acc.insert k (d.join v v')
    | none => acc.insert k v
  { vals := merged }

/-- Check equality for convergence detection -/
def beq (d : Domain α) (a b : AbsState α) : Bool :=
  a.vals.size == b.vals.size &&
  a.vals.fold (init := true) fun acc k v =>
    acc && match b.vals.get? k with
    | some v' => d.eq v v'
    | none => false

end AbsState

/-- A forward dataflow analysis specification) -/
structure ForwardSpec (α : Type) where
  /-- The abstract value domain -/
  domain : Domain α
  /-- Transfer function: process one non-phi statement, return updated state -/
  transfer : AbsState α → ClosedStmt → AbsState α
  /-- Resolve an operand to its abstract value in a given state -/
  resolveOp : AbsState α → Operand → α

/-- Precompute predecessor map for efficient CFG traversal -/
def buildPredMap (cfg : ClosedCFG) : Std.HashMap Nat (Array BlockId) :=
  cfg.allBlocks.foldl (init := {}) fun acc block =>
    block.successors.foldl (init := acc) fun acc' succId =>
      let preds := acc'.getD succId.id #[]
      acc'.insert succId.id (preds.push block.id)

/-- Result of a forward dataflow analysis: per-block exit states -/
structure ForwardResult (α : Type) where
  /-- Abstract state at exit of each block (after processing all statements) -/
  exitStates : Std.HashMap Nat (AbsState α)
  deriving Inhabited

namespace ForwardResult

/-- Get the exit state of a block, defaulting to empty -/
def getExitState (r : ForwardResult α) (blockId : Nat) : AbsState α :=
  r.exitStates.getD blockId {}

/-- Compute the entry state of a block by joining predecessor exit states -/
def blockEntryState (d : Domain α) (r : ForwardResult α)
    (predMap : Std.HashMap Nat (Array BlockId))
    (blockId : BlockId) (entryBlockId : BlockId)
    (initState : AbsState α) : AbsState α :=
  if blockId == entryBlockId then initState
  else
    let preds := predMap.getD blockId.id #[]
    preds.foldl (init := {}) fun acc predId =>
      match r.exitStates.get? predId.id with
      | some predExit => AbsState.join d acc predExit
      | none => acc

end ForwardResult

/-- Run a forward dataflow analysis to fixpoint -/
def forwardAnalysis (spec : ForwardSpec α) (cfg : ClosedCFG)
    (initState : AbsState α) (maxIters : Nat := 30) : ForwardResult α := Id.run do
  let rpo := cfg.reversePostorder
  let predMap := buildPredMap cfg

  let mut exitStates : Std.HashMap Nat (AbsState α) := {}

  for _iter in [:maxIters] do
    let mut changed := false

    for bid in rpo do
      let entryState := if bid == cfg.entry then
        initState
      else
        let preds := predMap.getD bid.id #[]
        preds.foldl (init := {}) fun acc predId =>
          match exitStates.get? predId.id with
          | some predExit => AbsState.join spec.domain acc predExit
          | none => acc

      let some block := cfg.getBlock bid | continue
      let mut state := entryState

      for stmt in block.stmts do
        match stmt.inst, stmt.result with
        | .phi incoming _, some rid =>
          let phiVal := incoming.foldl (init := spec.domain.bot) fun acc (op, predBid) =>
            let predState := exitStates.getD predBid.id {}
            let opVal := spec.resolveOp predState op
            spec.domain.join acc opVal
          state := state.set rid.id phiVal
        | _, _ => pure ()

      for stmt in block.stmts do
        match stmt.inst with
        | .phi _ _ => pure ()
        | _ => state := spec.transfer state stmt

      let prevExit := exitStates.getD bid.id {}
      if !AbsState.beq spec.domain state prevExit then
        changed := true
        exitStates := exitStates.insert bid.id state

    if !changed then break

  return { exitStates }

end Somac.Alloy.Analysis
