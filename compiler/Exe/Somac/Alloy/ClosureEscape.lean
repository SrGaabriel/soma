import Somac.Alloy.Func
import Std.Data.HashMap
import Std.Data.HashSet

namespace Somac.Alloy.ClosureEscape

open Somac.Alloy

/-- Statistics from the closure-escape analysis pass -/
structure EscapeStats where
  /-- makeClosure / makeClosurePoly results rewritten to stack allocation -/
  promoted : Nat := 0
  /-- Paired `erase` instructions removed as a consequence -/
  erasesEliminated : Nat := 0
  deriving Inhabited

namespace EscapeStats

def merge (a b : EscapeStats) : EscapeStats :=
  { promoted := a.promoted + b.promoted
  , erasesEliminated := a.erasesEliminated + b.erasesEliminated
  }

def isEmpty (s : EscapeStats) : Bool :=
  s.promoted == 0 && s.erasesEliminated == 0

end EscapeStats

/-- Collect the set of locals that hold a closure result -/
private def collectClosureResults (f : ClosedFunc) : Std.HashSet Nat := Id.run do
  let mut result : Std.HashSet Nat := {}
  let some cfg := f.body | return result
  for block in cfg.allBlocks do
    for stmt in block.stmts do
      match stmt.inst, stmt.result with
      | .makeClosure _ _, some rid => result := result.insert rid.id
      | .makeClosurePoly _ _ _, some rid => result := result.insert rid.id
      | _, _ => pure ()
  result

/-- Is `op` a reference to the closure local `cid`? -/
@[inline] private def opIs (cid : Nat) : Operand → Bool
  | .local id => id.id == cid
  | _ => false

/-- Does any operand in `ops` refer to closure local `cid`? -/
@[inline] private def anyIs (cid : Nat) (ops : Array Operand) : Bool :=
  ops.any (opIs cid)

/- TODO: standardize this logic -/
/-- Classify an instruction's use of closure local `cid` as safe or escaping -/
private def isSafeUse (cid : Nat) (inst : ClosedInst) : Bool :=
  let is := opIs cid
  let operands := inst.operands
  if !operands.any is then true
  else
    match inst with
    | .callClosure callee args _ =>
      is callee && !anyIs cid args
    | .closureFunc op => is op
    | .closureEnv op => is op
    | .erase op _ => is op
    | .clone op _ _ => is op
    | _ => false

/-- Does `term` reference closure local `cid` -/
@[inline] private def terminatorEscapes (cid : Nat) (term : Terminator) : Bool :=
  match term with
  | .ret (.local id) => id.id == cid
  | _ => false

/-- Determines whether any use is unsafe and returns the set of escaping locals -/
private def findEscapingClosures (f : ClosedFunc) (candidates : Std.HashSet Nat)
    : Std.HashSet Nat := Id.run do
  let mut escaping : Std.HashSet Nat := {}
  let some cfg := f.body | return escaping
  for block in cfg.allBlocks do
    for stmt in block.stmts do
      let producedHere : Option Nat :=
        match stmt.inst, stmt.result with
        | .makeClosure _ _, some rid => some rid.id
        | .makeClosurePoly _ _ _, some rid => some rid.id
        | _, _ => none
      for cid in candidates do
        if escaping.contains cid then continue
        if producedHere == some cid then continue
        if !isSafeUse cid stmt.inst then
          escaping := escaping.insert cid
    for cid in candidates do
      if escaping.contains cid then continue
      if terminatorEscapes cid block.terminator then
        escaping := escaping.insert cid
  escaping

/-- Rewrite a single function: promote non-escaping closure results to stack
    allocation and drop their paired `erase` instructions -/
private def rewriteFunc (f : ClosedFunc) : ClosedFunc × EscapeStats := Id.run do
  let candidates := collectClosureResults f
  if candidates.isEmpty then return (f, {})
  let escaping := findEscapingClosures f candidates
  if candidates.size == escaping.size then return (f, {})

  -- Materialize the set to avoid HashSet arithmetic on each lookup
  let promoted : Std.HashSet Nat := candidates.fold (init := ({} : Std.HashSet Nat))
    fun acc cid => if escaping.contains cid then acc else acc.insert cid

  if promoted.isEmpty then return (f, {})

  let some cfg := f.body | return (f, {})

  let mut erasesEliminated : Nat := 0
  let mut newBlocks : Std.HashMap Nat ClosedBlock := {}

  for (bid, block) in cfg.blocks do
    let mut newStmts : Array ClosedStmt := Array.mkEmpty block.stmts.size
    for stmt in block.stmts do
      match stmt.inst, stmt.result with
      | .makeClosure ref env, some rid =>
        if promoted.contains rid.id then
          newStmts := newStmts.push
            { stmt with inst := .stackClosure ref env }
        else
          newStmts := newStmts.push stmt
      | .makeClosurePoly ref tys env, some rid =>
        if promoted.contains rid.id then
          newStmts := newStmts.push
            { stmt with inst := .stackClosurePoly ref tys env }
        else
          newStmts := newStmts.push stmt
      | .erase (.local id) _, _ =>
        if promoted.contains id.id then
          erasesEliminated := erasesEliminated + 1
        else
          newStmts := newStmts.push stmt
      | _, _ =>
        newStmts := newStmts.push stmt
    newBlocks := newBlocks.insert bid { block with stmts := newStmts }

  let newFunc : ClosedFunc := { f with body := some { cfg with blocks := newBlocks } }
  pure (newFunc, { promoted := promoted.size, erasesEliminated })

/-- Run closure-escape analysis on every monomorphic function in the module -/
def escapeModule (m : Module) : Module × EscapeStats := Id.run do
  let mut stats : EscapeStats := {}
  let mut newFuncs : Array SomeFunc := Array.mkEmpty m.funcs.size
  for sf in m.funcs do
    match sf.asMono? with
    | none =>
      newFuncs := newFuncs.push sf
    | some f =>
      let (newF, funcStats) := rewriteFunc f
      stats := stats.merge funcStats
      newFuncs := newFuncs.push (SomeFunc.ofMono newF)
  pure ({ m with funcs := newFuncs }, stats)

end Somac.Alloy.ClosureEscape
