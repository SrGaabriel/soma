import Somac.Alloy.Func
import Somac.Alloy.DefUse
import Std.Data.HashMap
import Std.Data.HashSet

namespace Somac.Alloy.Borrow

open Somac.Alloy
open Somac.Alloy.DefUse

/-- Per-function borrow information: which parameters are borrowable -/
structure FuncBorrowInfo where
  funcId : FuncId
  borrowed : Array Bool
  deriving Inhabited

namespace FuncBorrowInfo

def isBorrowed (info : FuncBorrowInfo) (paramIdx : Nat) : Bool :=
  info.borrowed.getD paramIdx false

def markNotBorrowed (info : FuncBorrowInfo) (paramIdx : Nat) : FuncBorrowInfo :=
  if h : paramIdx < info.borrowed.size then
    { info with borrowed := info.borrowed.set paramIdx false }
  else info

end FuncBorrowInfo

/-- Module-level borrow analysis result: FuncId.id → FuncBorrowInfo -/
structure BorrowResult where
  info : Std.HashMap Nat FuncBorrowInfo
  deriving Inhabited

namespace BorrowResult

def get? (r : BorrowResult) (funcId : Nat) : Option FuncBorrowInfo :=
  r.info.get? funcId

def isBorrowed (r : BorrowResult) (funcId : Nat) (paramIdx : Nat) : Bool :=
  match r.info.get? funcId with
  | some info => info.isBorrowed paramIdx
  | none => false

end BorrowResult

/-- Check if an instruction escapes a local into an owned position -/
private def instEscapesLocal (inst : ClosedInst) (lid : LocalId) : Bool :=
  let isOp (op : Operand) : Bool := match op with
    | .local id => id == lid
    | _ => false
  match inst with
  -- Criterion 1: stored in heap ADT
  | .taggedLit _ fields _ => fields.any isOp
  | .reuseTaggedLit _ fields _ _ => fields.any isOp
  | .structLit fields _ => fields.any isOp
  | .arrayLit elems _ => elems.any isOp
  -- Criterion 2: captured in closure env
  | .makeClosure _ env => isOp env
  | .makeClosurePoly _ _ env => isOp env
  | .makeClosureDyn _ env _ => isOp env
  -- Criterion 4: wrapped in SUP
  | .lazySup _ src _ => isOp src
  -- Storing to memory
  | .store val _ => isOp val
  -- Criterion 5: passed as argument to unknown callee
  | .callIndirect _ args _ => args.any isOp
  | .callClosure _ args _ => args.any isOp
  | .callExtern _ args _ => args.any isOp
  | .callExternPoly _ _ args _ => args.any isOp
  | _ => false

/-- Check if a terminator returns a local -/
private def terminatorReturnsLocal (term : Terminator) (lid : LocalId) : Bool :=
  match term with
  | .ret (.local id) => id == lid
  | _ => false

/-- Intra-procedural analysis -/
private def initialScan (f : ClosedFunc) : FuncBorrowInfo := Id.run do
  let paramCount := f.sig.params.size
  if paramCount == 0 then
    return { funcId := f.id, borrowed := #[] }

  let mut borrowed : Array Bool := (Array.range paramCount).map (fun _ => true)

  let some cfg := f.body | return { funcId := f.id, borrowed }

  for block in cfg.allBlocks do
    for stmt in block.stmts do
      for pi in [:paramCount] do
        if borrowed[pi]! then
          let paramLid : LocalId := ⟨pi⟩
          if instEscapesLocal stmt.inst paramLid then
            borrowed := borrowed.set! pi false

    for pi in [:paramCount] do
      if borrowed[pi]! then
        let paramLid : LocalId := ⟨pi⟩
        if terminatorReturnsLocal block.terminator paramLid then
          borrowed := borrowed.set! pi false

  return { funcId := f.id, borrowed }

/-- Collect call sites within a function -/
private def collectCallSites (f : ClosedFunc) : Array (FuncId × Array Operand) := Id.run do
  let some cfg := f.body | return #[]
  let mut sites : Array (FuncId × Array Operand) := #[]

  for block in cfg.allBlocks do
    for stmt in block.stmts do
      match stmt.inst with
      | .call funcId args _ => sites := sites.push (funcId, args)
      | .callPoly funcId _ args _ => sites := sites.push (funcId, args)
      | _ => pure ()

  return sites

/-- Build the direct call graph: caller FuncId.id → Array of callee FuncId.ids -/
private def buildCallGraph
    (funcs : Array ClosedFunc)
    (callSitesMap : Std.HashMap Nat (Array (FuncId × Array Operand)))
    : Std.HashMap Nat (Array Nat) := Id.run do
  let mut graph : Std.HashMap Nat (Array Nat) := {}
  for f in funcs do
    let fid := f.id.id
    let mut callees : Array Nat := #[]
    for (calleeId, _) in callSitesMap.getD fid #[] do
      callees := callees.push calleeId.id
    graph := graph.insert fid callees
  return graph

/-- Tarjan's SCC algorithm -/
private def tarjanSCC (nodeIds : Array Nat) (graph : Std.HashMap Nat (Array Nat))
    : Array (Array Nat) := Id.run do
  let mut index : Nat := 0
  let mut nodeIndex : Std.HashMap Nat Nat := {}
  let mut nodeLowlink : Std.HashMap Nat Nat := {}
  let mut onStack : Std.HashSet Nat := {}
  let mut stack : Array Nat := #[]
  let mut sccs : Array (Array Nat) := #[]
  -- iterative Tarjan: explicit frame stack avoids deep recursion
  -- frame = (node, successorIndex, isReturning)
  let mut frames : Array (Nat × Nat × Bool) := #[]

  for startNode in nodeIds do
    if nodeIndex.contains startNode then continue

    frames := frames.push (startNode, 0, false)

    while h : frames.size > 0 do
      let (v, si, _) := frames[frames.size - 1]!
      frames := frames.pop

      if si == 0 && !nodeIndex.contains v then
        nodeIndex := nodeIndex.insert v index
        nodeLowlink := nodeLowlink.insert v index
        index := index + 1
        stack := stack.push v
        onStack := onStack.insert v

      let succs := graph.getD v #[]

      -- Find next unprocessed successor
      let mut si' := si
      let mut pushed := false
      while hsi : si' < succs.size do
        let w := succs[si']
        if !nodeIndex.contains w then
          frames := frames.push (v, si' + 1, true)
          frames := frames.push (w, 0, false)
          pushed := true
          break
        else if onStack.contains w then
          let vLow := nodeLowlink.getD v 0
          let wIdx := nodeIndex.getD w 0
          nodeLowlink := nodeLowlink.insert v (min vLow wIdx)
        si' := si' + 1

      if pushed then continue

      if nodeLowlink.getD v 0 == nodeIndex.getD v 0 then
        let mut scc : Array Nat := #[]
        let mut popping := true
        while popping do
          if stack.isEmpty then
            popping := false
          else
            let w := stack.back!
            stack := stack.pop
            onStack := onStack.erase w
            scc := scc.push w
            if w == v then popping := false
        sccs := sccs.push scc

      -- Propagate lowlink to parent
      if frames.size > 0 then
        let (parent, _, _) := frames[frames.size - 1]!
        let parentLow := nodeLowlink.getD parent 0
        let vLow := nodeLowlink.getD v 0
        nodeLowlink := nodeLowlink.insert parent (min parentLow vLow)

  return sccs

/-- Inter-procedural fixpoint using SCC-based iteration -/
private def interproceduralFixpoint
    (funcs : Array ClosedFunc)
    (initial : Std.HashMap Nat FuncBorrowInfo)
    : Std.HashMap Nat FuncBorrowInfo := Id.run do
  let mut info := initial

  let mut callSitesMap : Std.HashMap Nat (Array (FuncId × Array Operand)) := {}
  for f in funcs do
    callSitesMap := callSitesMap.insert f.id.id (collectCallSites f)

  let callGraph := buildCallGraph funcs callSitesMap
  let nodeIds := funcs.map (·.id.id)
  let sccs := tarjanSCC nodeIds callGraph

  for scc in sccs do
    for _ in [:scc.size + 1] do
      let mut changed := false

      for fid in scc do
        let some fInfo := info.get? fid | continue
        let callSites := callSitesMap.getD fid #[]

        let mut newInfo := fInfo

        for (calleeId, args) in callSites do
          let some calleeInfo := info.get? calleeId.id | continue

          for h : argIdx in [:args.size] do
            if argIdx < calleeInfo.borrowed.size && !calleeInfo.borrowed[argIdx]! then
              if h2 : argIdx < args.size then
                match args[argIdx] with
                | .local paramLid =>
                  let paramIdx := paramLid.id
                  if paramIdx < newInfo.borrowed.size && newInfo.borrowed[paramIdx]! then
                    newInfo := newInfo.markNotBorrowed paramIdx
                    changed := true
                | _ => pure ()

        info := info.insert fid newInfo

      if !changed then break

  return info

/-- Check whether a use of `lid` in `inst` is operand-read-only -/
private def isOperandReadOnly (borrowResult : BorrowResult) (inst : ClosedInst) (lid : Nat) : Bool :=
  let is (op : Operand) : Bool := match op with | .local id => id.id == lid | _ => false
  match inst with
  -- Projections: read source, produce derived value
  | .extractField op _ => is op
  | .getTag op => is op
  | .getPayload op _ _ _ => is op
  | .closureFunc op => is op
  | .closureEnv op => is op
  | .supProj0 op _ => is op
  | .supProj1 op _ => is op
  -- Pure value reads
  | .copy op => is op
  | .binOp _ l r _ => is l || is r
  | .unOp _ op => is op
  | .select c t e => is c || is t || is e
  | .load op _ => is op
  -- Address computations
  | .getFieldPtr op _ _ => is op
  | .getElemPtr op _ _ => is op
  -- Closure/indirect call: function operand is read-only, args are consumed
  | .callClosure f args _ => if args.any is then false else is f
  | .callIndirect f args _ => if args.any is then false else is f
  -- Direct call: read-only iff every position where lid appears is borrowed
  | .call calleeId args _ => Id.run do
    for ai in [:args.size] do
      if h : ai < args.size then
        if is args[ai] then
          if !borrowResult.isBorrowed calleeId.id ai then return false
    return true
  -- Clone source: clone reads the value to copy it
  | .clone op _ _ => is op
  -- Erase: releases ownership (but removed for borrowed values)
  | .erase op _ => is op
  | _ => false

/-- Check whether a terminator use of `lid` is read-only -/
private def isTermReadOnly (term : Terminator) (lid : Nat) : Bool :=
  match term with
  | .ret (.local id) => id.id != lid
  | _ => true

/-- If `inst` is a refcounted projection that reads from `lid` -/
private def rcProjectionOf? (inst : ClosedInst) (resultId : Option LocalId) (lid : Nat) : Option Nat :=
  let is (op : Operand) := match op with | .local id => id.id == lid | _ => false
  match inst with
  | .extractField op _ | .getPayload op _ _ _ | .closureEnv op
  | .supProj0 op _ | .supProj1 op _ =>
    if is op then resultId.map (·.id) else none
  | _ => none

/-- Check if removing ownership of `lid` is transitively safe through all
    projection chains -/
private def isTransitivelySafe
    (borrowResult : BorrowResult) (duInfo : DefUseInfo)
    (blocks : Std.HashMap Nat ClosedBlock)
    (startLid : Nat) : Bool := Id.run do
  let mut worklist : Array Nat := #[startLid]
  let mut visited : Std.HashSet Nat := {}
  while worklist.size > 0 do
    let cur := worklist.back!
    worklist := worklist.pop
    if visited.contains cur then continue
    visited := visited.insert cur
    let useLocs := duInfo.uses.getD cur #[]
    for loc in useLocs do
      let some block := blocks.get? loc.blockId | return false
      if h : loc.stmtIdx < block.stmts.size then
        let stmt := block.stmts[loc.stmtIdx]
        if !isOperandReadOnly borrowResult stmt.inst cur then
          return false
        if let some projId := rcProjectionOf? stmt.inst stmt.result cur then
          worklist := worklist.push projId
      else
        if !isTermReadOnly block.terminator cur then
          return false
  return true

/-- If `inst` is a projection with result type info (narrowable), return (resultId, resultTy) -/
private def narrowableProjectionInfo? (inst : ClosedInst) (resultId : Option LocalId) (lid : Nat)
    : Option (Nat × ClosedTy) :=
  let is (op : Operand) := match op with | .local id => id.id == lid | _ => false
  match inst with
  | .getPayload op _ _ ty => if is op then resultId.map fun r => (r.id, ty) else none
  | .supProj0 op ty => if is op then resultId.map fun r => (r.id, ty) else none
  | .supProj1 op ty => if is op then resultId.map fun r => (r.id, ty) else none
  | _ => none

/-- Rewrite statistics -/
structure RewriteStats where
  clonesEliminated : Nat := 0
  clonesNarrowed : Nat := 0
  erasesEliminated : Nat := 0
  deriving Inhabited

/-- Rewrite a function to eliminate or narrow redundant clones -/
private def rewriteFunc (f : ClosedFunc) (borrowResult : BorrowResult) : ClosedFunc × RewriteStats := Id.run do
  let some cfg := f.body | return (f, {})
  let fid := f.id.id
  let some fInfo := borrowResult.get? fid | return (f, {})

  -- Collect borrowed parameter indices
  let mut borrowedParams : Std.HashSet Nat := {}
  for pi in [:fInfo.borrowed.size] do
    if fInfo.borrowed[pi]! then
      borrowedParams := borrowedParams.insert pi
  if borrowedParams.isEmpty then return (f, {})

  let duInfo := DefUse.analyze f

  -- Build clone source map and metadata
  let mut cloneSourceMap : Std.HashMap Nat Nat := {}
  let mut cloneMeta : Std.HashMap Nat (ClosedTy × UInt32) := {}
  for block in cfg.allBlocks do
    for stmt in block.stmts do
      match stmt.inst, stmt.result with
      | .clone (.local srcId) ty label, some resultId =>
        cloneSourceMap := cloneSourceMap.insert resultId.id srcId.id
        cloneMeta := cloneMeta.insert resultId.id (ty, label)
      | _, _ => pure ()
  if cloneSourceMap.isEmpty then return (f, {})

  -- Root source computation
  let rootSource := fun (startId : Nat) => Id.run do
    let mut src := startId
    for _ in [:100] do
      match cloneSourceMap.get? src with
      | some parentSrc => src := parentSrc
      | none => break
    return src

  -- Classify each clone
  let mut removable : Std.HashSet Nat := {}
  let mut narrowable : Std.HashMap Nat (Array (Nat × ClosedTy)) := {}

  for (resultId, _) in cloneSourceMap.toArray do
    if !borrowedParams.contains (rootSource resultId) then continue

    -- Full removal: transitively safe through all projection chains
    if isTransitivelySafe borrowResult duInfo cfg.blocks resultId then
      removable := removable.insert resultId
    else
      let useLocs := duInfo.uses.getD resultId #[]
      let mut allProjOrErase := true
      let mut demandingProjs : Array (Nat × ClosedTy) := #[]
      let mut hasNonNarrowable := false

      for loc in useLocs do
        if !allProjOrErase then break
        let some block := cfg.blocks.get? loc.blockId | do allProjOrErase := false; continue
        if h : loc.stmtIdx < block.stmts.size then
          let stmt := block.stmts[loc.stmtIdx]
          let inst := stmt.inst
          match rcProjectionOf? inst stmt.result resultId with
          | some projResultId =>
            -- If this is a refcounted projection we check if downstream demands ownership
            if !isTransitivelySafe borrowResult duInfo cfg.blocks projResultId then
              match narrowableProjectionInfo? inst stmt.result resultId with
              | some (_, ty) => demandingProjs := demandingProjs.push (projResultId, ty)
              | none => hasNonNarrowable := true
          | none =>
            -- Not a refcounted projection so it must be either erase, getTag, closureFunc, or clone source
            match inst with
            | .erase (.local id) _ => if id.id != resultId then allProjOrErase := false
            | .getTag (.local id) => if id.id != resultId then allProjOrErase := false
            | .closureFunc (.local id) => if id.id != resultId then allProjOrErase := false
            | .clone (.local id) _ _ => if id.id != resultId then allProjOrErase := false
            | _ => allProjOrErase := false
        else
          if !isTermReadOnly block.terminator resultId then
            allProjOrErase := false

      if allProjOrErase && !demandingProjs.isEmpty && !hasNonNarrowable then
        narrowable := narrowable.insert resultId demandingProjs

  if removable.isEmpty && narrowable.isEmpty then return (f, {})

  -- For removable and narrowable clones, follow chain to first non-removed source
  let mut transitiveSource : Std.HashMap Nat Nat := {}
  for (resultId, _) in cloneSourceMap.toArray do
    if removable.contains resultId || narrowable.contains resultId then
      let mut src := resultId
      for _ in [:100] do
        match cloneSourceMap.get? src with
        | some parentSrc =>
          if removable.contains src then src := parentSrc
          else break
        | none => break
      transitiveSource := transitiveSource.insert resultId src

  let mut erasesToRemove : Std.HashSet (Nat × Nat) := {}
  for block in cfg.allBlocks do
    let bid := block.id.id
    for h : i in [:block.stmts.size] do
      let stmt := block.stmts[i]
      match stmt.inst with
      | .erase (.local id) _ =>
        if removable.contains id.id || narrowable.contains id.id
           || borrowedParams.contains id.id then
          erasesToRemove := erasesToRemove.insert (bid, i)
      | _ => pure ()

  let mut maxLocalId : Nat := 0
  for block in cfg.allBlocks do
    for stmt in block.stmts do
      if let some rid := stmt.result then
        maxLocalId := max maxLocalId rid.id
  let mut nextFreshId := maxLocalId + 1

  let mut narrowRemap : Std.HashMap Nat Nat := {}
  let mut narrowInsertAfter : Std.HashMap (Nat × Nat) (Nat × Nat × ClosedTy × UInt32) := {}

  for (cloneResultId, demandingProjs) in narrowable.toArray do
    let some (_, label) := cloneMeta.get? cloneResultId | continue
    for (projResultId, projTy) in demandingProjs do
      let freshId := nextFreshId
      nextFreshId := nextFreshId + 1
      narrowRemap := narrowRemap.insert projResultId freshId
      if let some defLoc := duInfo.defSite.get? projResultId then
        narrowInsertAfter := narrowInsertAfter.insert
          (defLoc.blockId, defLoc.stmtIdx)
          (projResultId, freshId, projTy, label)

  -- Build combined operand remapper
  let remapOp : Operand → Operand := fun op =>
    match op with
    | .local id =>
      -- Narrow remap takes priority (projection → narrow clone result)
      match narrowRemap.get? id.id with
      | some freshId => .local ⟨freshId⟩
      | none =>
        -- Then transitive source (removed/narrowed clone → original source)
        match transitiveSource.get? id.id with
        | some src => .local ⟨src⟩
        | none => op
    | _ => op

  let mut newBlocks : Std.HashMap Nat ClosedBlock := {}
  let mut stats : RewriteStats := {}

  for entry in cfg.blocks.toArray do
    let blockId := entry.1
    let block := entry.2
    let mut newStmts : Array ClosedStmt := #[]

    for h : i in [:block.stmts.size] do
      let stmt := block.stmts[i]

      if let some rid := stmt.result then
        if removable.contains rid.id then
          stats := { stats with clonesEliminated := stats.clonesEliminated + 1 }
          continue

      if let some rid := stmt.result then
        if narrowable.contains rid.id then
          stats := { stats with clonesNarrowed := stats.clonesNarrowed + 1 }
          continue

      if erasesToRemove.contains (blockId, i) then
        stats := { stats with erasesEliminated := stats.erasesEliminated + 1 }
        continue

      -- Remap operands and emit
      let newInst := stmt.inst.mapOperands remapOp
      newStmts := newStmts.push { stmt with inst := newInst }

      -- Insert narrow clone after demanding projections
      if let some (projResultId, freshId, ty, label) := narrowInsertAfter.get? (blockId, i) then
        newStmts := newStmts.push {
          result := some ⟨freshId⟩,
          inst := .clone (.local ⟨projResultId⟩) ty label
        }

    -- Remap terminator operands
    let newTerm := block.terminator.mapOperands remapOp
    newBlocks := newBlocks.insert blockId { block with stmts := newStmts, terminator := newTerm }

  let newCfg := { cfg with blocks := newBlocks }
  return ({ f with body := some newCfg }, stats)

/-- Count the number of borrowed parameters across all functions -/
private def countBorrowed (result : BorrowResult) : Nat :=
  result.info.toArray.foldl (init := 0) fun acc (_, info) =>
    acc + info.borrowed.foldl (init := 0) fun a b => if b then a + 1 else a

/-- Borrow analysis results -/
structure BorrowStats where
  borrowedParams : Nat := 0
  clonesEliminated : Nat := 0
  clonesNarrowed : Nat := 0
  erasesEliminated : Nat := 0
  paramInfo : Std.HashMap Nat (Array Bool) := {}

/-- Run borrow analysis on a module -/
def borrowModule (m : Module) : Module × BorrowStats := Id.run do
  let monoFuncs := m.monoFuncs

  if monoFuncs.isEmpty then
    return (m, {})

  -- Intra-procedural scan
  let mut initial : Std.HashMap Nat FuncBorrowInfo := {}
  for f in monoFuncs do
    let info := initialScan f
    initial := initial.insert f.id.id info

  -- Inter-procedural fixpoint
  let finalInfo := interproceduralFixpoint monoFuncs initial
  let result : BorrowResult := { info := finalInfo }

  let borrowedCount := countBorrowed result

  if borrowedCount == 0 then
    return (m, {})

  -- Projection-aware clone narrowing
  let mut newFuncs : Array SomeFunc := #[]
  let mut paramInfo : Std.HashMap Nat (Array Bool) := {}
  for (fid, fInfo) in finalInfo.toArray do
    paramInfo := paramInfo.insert fid fInfo.borrowed

  let mut totalStats : BorrowStats := { borrowedParams := borrowedCount, paramInfo }

  for sf in m.funcs do
    match sf.asMono? with
    | some f =>
      let (rewritten, stats) := rewriteFunc f result
      newFuncs := newFuncs.push (SomeFunc.ofMono rewritten)
      totalStats := {
        totalStats with
        clonesEliminated := totalStats.clonesEliminated + stats.clonesEliminated
        clonesNarrowed := totalStats.clonesNarrowed + stats.clonesNarrowed
        erasesEliminated := totalStats.erasesEliminated + stats.erasesEliminated
      }
    | none => newFuncs := newFuncs.push sf

  return ({ m with funcs := newFuncs }, totalStats)

end Somac.Alloy.Borrow
