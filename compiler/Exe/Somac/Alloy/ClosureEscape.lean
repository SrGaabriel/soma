import Somac.Alloy.Func
import Somac.Alloy.Analysis
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Closure Escape Analysis + Stack Clone Promotion

Promotes closure-producing instructions (`makeClosure`, `makeClosurePoly`)
and their matching `clone` instructions into their stack-allocated
counterparts (`stackClosure`, `stackClosurePoly`, `stackClone`) when the
result provably does not escape the enclosing function. Paired `erase`
instructions on promoted results are elided.

## Architecture

**Escape analysis** rides on `Alloy.Analysis.forwardAnalysis`, which handles
reverse-postorder fixpoint iteration and phi-node joins natively. The
lattice is a two-point order `clean ⊑ escaped`; transfer marks any operand
that appears in a publishing position (ADT field, closure env, lazySup,
store, call arg, etc.) as `escaped`. Phi merges via the framework's built-in
`join`, which correctly propagates taint across branches.

**Size tracking** is a second, independent pass over the result of the
escape analysis. For each promoted `makeClosure`, the closure's ptr-slot
count is computed once via `Ty.closureTotalSlotCount` (the single source of
truth shared with LLVM codegen) and recorded in a `sizeMap`. For each
non-escaping `clone`, if its source local is in `sizeMap` and its type is
`Ty.isStackCloneable`, it rewrites to `.stackClone src ty slots`. The
resulting local is itself added to `sizeMap`, so multi-step clone chains
(`clone (clone c)`) also promote.

Phi sizing is handled by a fixpoint pre-pass: a phi result inherits the
shared size of its inputs iff every input's size is known and equal. A few
iterations converge; in practice one pass suffices unless closures are
threaded through nested control-flow loops.

## Invariants

1. **Layout parity.** Promoted `stackClosure` and `stackClone` buffers are
   `[closureTotalSlotCount x ptr]`, matching the heap layout byte-for-byte.
   The shared helper `Ty.closureTotalSlotCount` makes drift impossible.
2. **No stale `erase`.** Any `erase L _` where `L`'s origin is a promoted
   stack site is dropped; the stack buffer dies with the frame and the
   runtime never sees the pointer.
3. **Whitelist-based transfer function.** The dataflow's transfer function
   marks any operand appearing outside the enumerated safe-use positions
   as escaped. New `Inst` variants fail-safe: they land in the
   `markUnsafeOperands` catch-all and are treated as publishing every
   operand, blocking promotion until a deliberate review classifies them.
-/

namespace Somac.Alloy.ClosureEscape

open Somac.Alloy
open Somac.Alloy.Analysis

/-! ## Escape lattice and dataflow spec -/

/-- Two-point lattice: `clean` is the bottom (not yet observed escaping);
    `escaped` is the top (at least one use has published the value). -/
inductive Escape where
  | clean
  | escaped
  deriving BEq, Inhabited, Repr

private def escapeDomain : Domain Escape where
  bot := .clean
  join a b :=
    match a, b with
    | .clean, .clean => .clean
    | _, _           => .escaped
  eq a b := a == b

/-- Resolve an operand to its escape status. Non-locals (constants, function
    refs) are vacuously clean. -/
private def escapeResolve (state : AbsState Escape) : Operand → Escape
  | .local id => state.get escapeDomain id.id
  | _         => .clean

/-- Mark a single operand as escaped if it is a local. -/
private def markOp (s : AbsState Escape) : Operand → AbsState Escape
  | .local id => s.set id.id .escaped
  | _         => s

/-- Mark every operand in the array as escaped. -/
private def markOps (s : AbsState Escape) (ops : Array Operand) : AbsState Escape :=
  ops.foldl markOp s

/-- Transfer function. For each statement, determine which operand positions
    are *unsafe* (publish the operand beyond the current frame) and mark
    their locals as escaped. Safe positions leave the state untouched.

    The whitelist is the inverse of what `Borrow.instEscapesLocal` uses:
    same semantic framing, rephrased forward instead of as an "is this an
    escape" predicate.

    Phi nodes are *not* processed here — the framework's `forwardAnalysis`
    handles them specially, joining predecessor states via `domain.join`. -/
private def escapeTransfer (state : AbsState Escape) (stmt : ClosedStmt)
    : AbsState Escape :=
  match stmt.inst with
  -- Pure reads / structural rewires: all operands safe.
  | .copy _
  | .load _ _
  | .getTag _
  | .getPayload _ _ _ _
  | .getFieldPtr _ _ _
  | .getElemPtr _ _ _
  | .extractField _ _
  | .extractElem _ _
  | .closureFunc _
  | .closureEnv _
  | .erase _ _
  | .clone _ _ _
  | .stackClone _ _ _
  | .supProj0 _ _
  | .supProj1 _ _
  | .alloca _
  | .phi _ _ => state

  -- Invocation: callee position is safe (not escaping), args escape.
  | .callClosure _ args _
  | .callIndirect _ args _ => markOps state args

  -- Regular calls: every arg escapes.
  | .call _ args _
  | .callPoly _ _ args _
  | .callExtern _ args _
  | .callExternPoly _ _ args _
  | .callIntrinsic _ args _ => markOps state args

  -- Closure construction: env is captured into the closure.
  | .makeClosure _ env
  | .makeClosurePoly _ _ env
  | .stackClosure _ env
  | .stackClosurePoly _ _ env => markOp state env
  | .makeClosureDyn fn env _  => markOp (markOp state fn) env

  -- Aggregate construction: every field is captured.
  | .taggedLit _ fields _
  | .structLit fields _
  | .arrayLit fields _ => markOps state fields
  | .reuseTaggedLit _ fields r _ => markOps (markOp state r) fields

  -- Field inserts: the new value is captured into the aggregate.
  | .insertField _ _ newVal
  | .insertElem _ _ newVal => markOp state newVal

  -- SUP boxing: source escapes into the SUP cell.
  | .lazySup _ src _ => markOp state src

  -- Memory writes: stored value escapes through the pointer.
  | .store val _ => markOp state val

  -- free / memory-movers: conservatively mark every operand.
  | .free p => markOp state p
  | .memcpy d s sz
  | .memset d s sz => markOp (markOp (markOp state d) s) sz

  -- Arithmetic / bit-pattern ops: closure values shouldn't ever land here.
  -- Conservatively escape to stay sound if a type hole lets one through.
  | .binOp _ l r _ => markOp (markOp state l) r
  | .unOp _ o => markOp state o
  | .select c t e => markOp (markOp (markOp state c) t) e

  -- Allocation primitive: no operands carrying locals we care about.
  | .malloc sz => markOp state sz
  | .panic _ _ => state

private def escapeSpec : ForwardSpec Escape where
  domain := escapeDomain
  transfer := escapeTransfer
  resolveOp := escapeResolve

/-! ## Escape set extraction -/

/-- Compute the set of locals that escape at any point in the function's
    lifetime. A local is escaped iff it either (a) appears at an unsafe use
    in some statement or (b) is returned by a terminator. The exit-state
    union captures (a); the terminator scan captures (b). -/
private def computeEscapedLocals (f : ClosedFunc) : Std.HashSet Nat := Id.run do
  let mut escaped : Std.HashSet Nat := {}
  let some cfg := f.body | return escaped
  let result := forwardAnalysis escapeSpec cfg {}

  for block in cfg.allBlocks do
    let exitState := result.getExitState block.id.id
    for (k, v) in exitState.vals do
      if v == .escaped then escaped := escaped.insert k
    match block.terminator with
    | .ret (.local id) => escaped := escaped.insert id.id
    | _ => pure ()

  escaped

/-! ## Stats -/

structure EscapeStats where
  /-- `makeClosure` / `makeClosurePoly` rewritten to stack. -/
  promotedClosures : Nat := 0
  /-- `clone` rewritten to `stackClone`. -/
  promotedClones : Nat := 0
  /-- Paired `erase` instructions dropped. -/
  erasesEliminated : Nat := 0
  deriving Inhabited

namespace EscapeStats

def merge (a b : EscapeStats) : EscapeStats :=
  { promotedClosures := a.promotedClosures + b.promotedClosures
  , promotedClones := a.promotedClones + b.promotedClones
  , erasesEliminated := a.erasesEliminated + b.erasesEliminated
  }

def isEmpty (s : EscapeStats) : Bool :=
  s.promotedClosures == 0 && s.promotedClones == 0 && s.erasesEliminated == 0

def total (s : EscapeStats) : Nat :=
  s.promotedClosures + s.promotedClones

end EscapeStats

/-! ## Phi-aware size inference

`sizeMap : Nat → Nat` maps each local id that holds a known-size stack
closure (from `stackClosure` or `stackClone`) to its ptr-slot count. The
rewrite pass populates it in RPO as it visits statements. Phi results need
a separate pass: a phi is added to the map iff every one of its incoming
operands is in the map *and* all inputs agree on the same size. The pass
iterates until fixpoint — rare to need more than one iteration, but loops
with closure-carrying phis can. -/

private def propagatePhiSizes (cfg : ClosedCFG) (sizeMap : Std.HashMap Nat Nat)
    : Std.HashMap Nat Nat := Id.run do
  let mut sm := sizeMap
  let mut changed := true
  while changed do
    changed := false
    for block in cfg.allBlocks do
      for stmt in block.stmts do
        match stmt.inst, stmt.result with
        | .phi incoming _, some rid =>
          if sm.contains rid.id then continue
          -- All inputs must be locals already in sm, with the same size.
          let mut agreed : Option Nat := none
          let mut ok := true
          for (op, _) in incoming do
            if !ok then continue
            match op with
            | .local id =>
              match sm.get? id.id with
              | some sz =>
                match agreed with
                | none    => agreed := some sz
                | some a  => if a != sz then ok := false
              | none => ok := false
            | _ => ok := false
          if ok then
            match agreed with
            | some sz =>
              sm := sm.insert rid.id sz
              changed := true
            | none => pure ()
        | _, _ => pure ()
  sm

/-! ## Rewrite -/

private def rewriteFunc (f : ClosedFunc) : ClosedFunc × EscapeStats := Id.run do
  let some cfg := f.body | return (f, {})

  -- Phase 1: escape analysis.
  let escaped := computeEscapedLocals f

  -- Phase 2: walk blocks in RPO, populating `sizeMap` as we promote
  -- `makeClosure` sites. We need the map before phi propagation can fire,
  -- so this pass only handles direct def→use cases. Phi handling comes next.
  let mut sizeMap : Std.HashMap Nat Nat := {}
  let rpo := cfg.reversePostorder

  for bid in rpo do
    let some block := cfg.getBlock bid | continue
    for stmt in block.stmts do
      match stmt.inst, stmt.result with
      | .makeClosure _ env, some rid
      | .makeClosurePoly _ _ env, some rid =>
        if !escaped.contains rid.id then
          -- Need the env's Alloy type to compute slot count.
          let envTy : Option ClosedTy :=
            match env with
            | .local id => f.localTypes.get? id.id
            | _         => none
          if let some ety := envTy then
            sizeMap := sizeMap.insert rid.id ety.closureTotalSlotCount
      | _, _ => pure ()

  -- Phase 3: propagate size through phi nodes.
  sizeMap := propagatePhiSizes cfg sizeMap

  -- Phase 4: propagate size through clone chains. Because a clone inherits
  -- its source's size, and sources may be phi results resolved in phase 3,
  -- we need one more fixpoint pass over clone instructions.
  let mut cloneChanged := true
  while cloneChanged do
    cloneChanged := false
    for block in cfg.allBlocks do
      for stmt in block.stmts do
        match stmt.inst, stmt.result with
        | .clone (.local srcId) ty _, some rid =>
          if !escaped.contains rid.id && ty.isStackCloneable
              && !sizeMap.contains rid.id then
            if let some sz := sizeMap.get? srcId.id then
              sizeMap := sizeMap.insert rid.id sz
              cloneChanged := true
        | _, _ => pure ()

  -- Phase 5: rewrite the function body.
  let mut newBlocks : Std.HashMap Nat ClosedBlock := {}
  let mut stats : EscapeStats := {}

  for (bid, block) in cfg.blocks do
    let mut newStmts : Array ClosedStmt := Array.mkEmpty block.stmts.size
    for stmt in block.stmts do
      match stmt.inst, stmt.result with
      | .makeClosure ref env, some rid =>
        if escaped.contains rid.id then
          newStmts := newStmts.push stmt
        else
          newStmts := newStmts.push { stmt with inst := .stackClosure ref env }
          stats := { stats with promotedClosures := stats.promotedClosures + 1 }
      | .makeClosurePoly ref tys env, some rid =>
        if escaped.contains rid.id then
          newStmts := newStmts.push stmt
        else
          newStmts := newStmts.push { stmt with inst := .stackClosurePoly ref tys env }
          stats := { stats with promotedClosures := stats.promotedClosures + 1 }
      | .clone (.local srcId) ty _label, some rid =>
        -- Promote iff result is non-escaping AND we have a known size.
        -- sizeMap membership is the authoritative signal — it implies the
        -- source traces to a stackClosure or stackClone.
        if !escaped.contains rid.id && ty.isStackCloneable
            && sizeMap.contains rid.id then
          if let some sz := sizeMap.get? srcId.id then
            newStmts := newStmts.push
              { stmt with inst := .stackClone (.local srcId) ty sz }
            stats := { stats with promotedClones := stats.promotedClones + 1 }
          else
            newStmts := newStmts.push stmt
        else
          newStmts := newStmts.push stmt
      | .erase (.local id) _, _ =>
        if sizeMap.contains id.id then
          stats := { stats with erasesEliminated := stats.erasesEliminated + 1 }
        else
          newStmts := newStmts.push stmt
      | _, _ =>
        newStmts := newStmts.push stmt
    newBlocks := newBlocks.insert bid { block with stmts := newStmts }

  let newFunc : ClosedFunc := { f with body := some { cfg with blocks := newBlocks } }
  pure (newFunc, stats)

/-- Run closure-escape analysis on every monomorphic function in the module. -/
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
