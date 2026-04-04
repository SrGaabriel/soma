import Somac.Circuit.Graph
import Somac.Circuit.Node
import Soma.Core.Value
import Soma.Core.Eval
import Std.Data.HashMap
import Std.Data.HashSet

namespace Somac.Circuit.IOErasure

open Somac.Circuit.Graph (Graph NodeEntry Definition)
open Somac.Circuit.Node (Node NodeId PortId PortIdx)
open Soma.Core (Value Closure)
open Soma.Core.Closure (applyPure)

/-- Configuration for IO erasure at the Circuit IR level -/
structure IOErasureCtx where
  worldUid? : Option Nat := none
  pairUid? : Option Nat := none
  ioBindBookIdx? : Option Nat := none
  pureIOBookIdx? : Option Nat := none

private def isWorldTy (ctx : IOErasureCtx) (v : Value) : Bool :=
  match v with
  | .vPrimTy .world => true
  | .vDataType uid _ => ctx.worldUid?.any (· == uid.id)
  | _ => false

private def isIOPairTy (ctx : IOErasureCtx) (v : Value) : Bool :=
  match v with
  | .vSigma _ _ fst _ => isWorldTy ctx fst
  | .vDataType uid params =>
    ctx.pairUid?.any (· == uid.id) && match params with
      | fst :: _ :: _ => isWorldTy ctx fst
      | _ => false
  | _ => false

private def hasWorldDomain (ctx : IOErasureCtx) (ty : Value) : Bool :=
  match ty.piDomain? with
  | some dom => isWorldTy ctx dom
  | none => false

/-- Count explicit World parameters in a function type -/
private partial def countWorldParamsInType (ctx : IOErasureCtx) (ty : Value) : Nat :=
  match ty with
  | .vPi _ binder _ dom cod =>
    if binder.isImplicit && dom.isType then
      countWorldParamsInType ctx (applyPure cod (Value.vNeutral dom (.nVar ⟨"_", ⟨0⟩⟩)))
    else if isWorldTy ctx dom then
      1 + countWorldParamsInType ctx (applyPure cod (Value.vPrimTy .unit))
    else
      countWorldParamsInType ctx (applyPure cod (Value.vNeutral dom (.nVar ⟨"_", ⟨0⟩⟩)))
  | _ => 0

/-- Check if a node is a REF or ALO pointing to a specific book index -/
private def isBookRef (node : Node) (bookIdx : Nat) : Bool :=
  match node with
  | .ref rid => rid == bookIdx
  | .alo rid => rid == bookIdx
  | _ => false

/-- What kind of erasure to apply to a node -/
private inductive EraseAction where
  | worldLam    -- bypass LAM, ERA variable port
  | ioPairCtor  -- bypass CTOR to payload, ERA World field
  | ioPairMat   -- bypass MAT principal↔hit, ERA miss
  | worldApp    -- bypass APP principal↔function, ERA argument
  | ioPairProj0 -- replace with unit constant
  | ioPairProj1 -- bypass PROJ (identity)
  | pureIO      -- APP(REF(pure_io), x) → x (identity bypass)
  | ioBind (innerAppId : NodeId) (refId : NodeId)
      -- APP₂(APP₁(REF(io_bind), m), f) → APP₂(f, m)
      -- Rewire outer APP to apply f to m, remove inner APP and REF

/-- Link two ports: connect their external targets to each other, bypassing the node between -/
private def link (g : Graph) (portA portB : PortId) : Graph :=
  let targetA := g.getConnection portA
  let targetB := g.getConnection portB
  let g := g.disconnect portA
  let g := g.disconnect portB
  match targetA, targetB with
  | some a, some b =>
    if a == b then g
    else g.connect a b
  | _, _ => g

/-- Add an ERA node connected to a port -/
private def addEra (g : Graph) (target : PortId) : Graph :=
  let (eraId, g) := g.addNode .era (Value.vPrimTy .unit)
  g.connect (PortId.principal eraId) target

/-- Classify a node for IO erasure (read-only, no graph mutation) -/
private def classifyNode (g : Graph) (nodeId : NodeId) (ctx : IOErasureCtx)
    : Option EraseAction := do
  let entry ← g.getNode nodeId
  match entry.node with
  | .lam _ =>
    if hasWorldDomain ctx entry.ty then some .worldLam else none
  | .ctor tag arity =>
    if tag == 0 && arity == 2 then
      -- Check type annotation OR structural check (first field is World-typed)
      let isIO := isIOPairTy ctx entry.ty || match entry.getPort ⟨1⟩ with
        | some fstPort => match g.getNode fstPort.node with
          | some fstEntry => isWorldTy ctx fstEntry.ty
          | none => false
        | none => false
      if isIO then some .ioPairCtor else none
    else none
  | .mat _ =>
    let scrutTy := match entry.getPort ⟨1⟩ with
      | some scrutPort =>
        match g.getNode scrutPort.node with
        | some scrutEntry => scrutEntry.ty
        | none => entry.ty
      | none => entry.ty
    -- Check type annotation OR check if scrutinee is an IO Pair CTOR
    let isIO := isIOPairTy ctx scrutTy || match entry.getPort ⟨1⟩ with
      | some scrutPort => match g.getNode scrutPort.node with
        | some scrutEntry => match scrutEntry.node with
          | .ctor 0 2 => isIOPairTy ctx scrutEntry.ty ||
            match scrutEntry.getPort ⟨1⟩ with
            | some fstPort => match g.getNode fstPort.node with
              | some fstEntry => isWorldTy ctx fstEntry.ty
              | none => false
            | none => false
          | _ => false
        | none => false
      | none => false
    if isIO then some .ioPairMat else none
  | .app =>
    -- Check for io_bind pattern: APP₂(APP₁(REF(io_bind), m), f)
    if let some bindIdx := ctx.ioBindBookIdx? then
      if let some fnPort := entry.getPort ⟨1⟩ then
        if let some innerEntry := g.getNode fnPort.node then
          if let .app := innerEntry.node then
            if let some innerFnPort := innerEntry.getPort ⟨1⟩ then
              if let some refEntry := g.getNode innerFnPort.node then
                if isBookRef refEntry.node bindIdx then
                  return EraseAction.ioBind fnPort.node innerFnPort.node
    -- Check for pure_io pattern: APP(REF(pure_io), x)
    if let some pureIdx := ctx.pureIOBookIdx? then
      if let some fnPort := entry.getPort ⟨1⟩ then
        if let some refEntry := g.getNode fnPort.node then
          if isBookRef refEntry.node pureIdx then
            return EraseAction.pureIO
    -- Check for World APP (existing pattern)
    let fnExpectsWorld := match entry.getPort ⟨1⟩ with
      | some fnPort =>
        match g.getNode fnPort.node with
        | some fnEntry => hasWorldDomain ctx fnEntry.ty
        | none => false
      | none => false
    let argIsWorld := match entry.getPort ⟨2⟩ with
      | some argPort =>
        match g.getNode argPort.node with
        | some argEntry => isWorldTy ctx argEntry.ty
        | none => false
      | none => false
    if fnExpectsWorld || argIsWorld then some .worldApp else none
  | .proj fieldIdx =>
    let recordTy := match entry.getPort ⟨1⟩ with
      | some recPort =>
        match g.getNode recPort.node with
        | some recEntry => recEntry.ty
        | none => entry.ty
      | none => entry.ty
    if isIOPairTy ctx recordTy then
      if fieldIdx == 0 then some .ioPairProj0
      else if fieldIdx == 1 then some .ioPairProj1
      else none
    else none
  | _ => none

/-- Apply a single erasure action to the graph -/
private def applyErase (g : Graph) (nodeId : NodeId) (action : EraseAction)
    : Graph := Id.run do
  let some entry := g.getNode nodeId | return g
  let mut graph := g
  match action with
  | .worldLam =>
    -- Bypass: link principal(0) ↔ body(2)
    graph := link graph (PortId.principal nodeId) ⟨nodeId, ⟨2⟩⟩
    -- ERA the variable port (1) if connected to non-ERA
    if let some varTarget := entry.getPort ⟨1⟩ then
      graph := graph.disconnect ⟨nodeId, ⟨1⟩⟩
      let isEra := match graph.getNode varTarget.node with
        | some e => match e.node with | .era => true | _ => false
        | none => true
      if !isEra then graph := addEra graph varTarget
    graph := graph.removeNode nodeId

  | .ioPairCtor =>
    -- Bypass: link principal(0) ↔ payload(2), ERA World(1)
    graph := link graph (PortId.principal nodeId) ⟨nodeId, ⟨2⟩⟩
    if let some worldPort := entry.getPort ⟨1⟩ then
      graph := graph.disconnect ⟨nodeId, ⟨1⟩⟩
      graph := addEra graph worldPort
    graph := graph.removeNode nodeId

  | .ioPairMat =>
    -- Bypass: link principal(0) ↔ hit(2), ERA miss(3)
    graph := link graph (PortId.principal nodeId) ⟨nodeId, ⟨2⟩⟩
    if let some missPort := entry.getPort ⟨3⟩ then
      graph := graph.disconnect ⟨nodeId, ⟨3⟩⟩
      graph := addEra graph missPort
    graph := graph.disconnect ⟨nodeId, ⟨1⟩⟩
    graph := graph.removeNode nodeId

  | .worldApp =>
    -- Bypass: link principal(0) ↔ function(1), ERA argument(2)
    graph := link graph (PortId.principal nodeId) ⟨nodeId, ⟨1⟩⟩
    if let some argPort := entry.getPort ⟨2⟩ then
      graph := graph.disconnect ⟨nodeId, ⟨2⟩⟩
      graph := addEra graph argPort
    graph := graph.removeNode nodeId

  | .ioPairProj0 =>
    -- Replace with unit constant
    graph := graph.disconnect ⟨nodeId, ⟨1⟩⟩
    let (unitId, graph') := graph.addNode (.num .u64 0) (Value.vPrimTy .unit)
    graph := graph'
    if let some consumer := entry.getPrincipal then
      graph := graph.disconnect (PortId.principal nodeId)
      graph := graph.connect (PortId.principal unitId) consumer
    graph := graph.removeNode nodeId

  | .ioPairProj1 =>
    -- Bypass: link principal(0) ↔ record(1)
    graph := link graph (PortId.principal nodeId) ⟨nodeId, ⟨1⟩⟩
    graph := graph.removeNode nodeId

  | .pureIO =>
    -- pure_io x → x: bypass APP(REF(pure_io), x)
    -- Link principal(0) ↔ argument(2), ERA the REF
    graph := link graph (PortId.principal nodeId) ⟨nodeId, ⟨2⟩⟩
    if let some refPort := entry.getPort ⟨1⟩ then
      graph := graph.disconnect ⟨nodeId, ⟨1⟩⟩
      graph := addEra graph refPort
    graph := graph.removeNode nodeId

  | .ioBind innerAppId refId =>
    let some innerEntry := graph.getNode innerAppId | return graph
    let fTarget := entry.getPort ⟨2⟩ -- where f connects externally
    let mTarget := innerEntry.getPort ⟨2⟩ -- where m connects externally
    let refTarget := innerEntry.getPort ⟨1⟩ -- the REF node port

    -- Disconnect all involved ports
    graph := graph.disconnect ⟨nodeId, ⟨1⟩⟩
    graph := graph.disconnect ⟨nodeId, ⟨2⟩⟩
    graph := graph.disconnect ⟨innerAppId, ⟨1⟩⟩
    graph := graph.disconnect ⟨innerAppId, ⟨2⟩⟩

    -- Reconnect: APP₂.function = f, APP₂.argument = m
    if let some ft := fTarget then
      graph := graph.connect ⟨nodeId, ⟨1⟩⟩ ft
    if let some mt := mTarget then
      graph := graph.connect ⟨nodeId, ⟨2⟩⟩ mt

    -- ERA the REF/ALO node for io_bind
    if let some rt := refTarget then
      graph := addEra graph rt

    -- Remove the inner APP₁
    graph := graph.removeNode innerAppId

  graph

/-- Classify all nodes and collect erasure targets (pure, no mutation) -/
private def collectTargets (graph : Graph) (ctx : IOErasureCtx)
    : Array (NodeId × EraseAction) :=
  graph.nodes.fold (init := #[]) fun acc id _ =>
    match classifyNode graph ⟨id⟩ ctx with
    | some action => acc.push (⟨id⟩, action)
    | none => acc

/-- Build definition root → index map -/
private def buildRootMap (graph : Graph) : Std.HashMap Nat Nat :=
  (List.range graph.book.size).foldl (init := {}) fun acc i =>
    match graph.book[i]? with
    | some def_ => acc.insert def_.root.id i
    | none => acc

/-- State threaded through the erasure passes -/
private structure EraseState where
  graph : Graph
  rootMap : Std.HashMap Nat Nat
  count : Nat := 0
  defWorldLams : Std.HashMap Nat Nat := {}

/-- Process a single World LAM target -/
private def processOneWorldLam (s : EraseState) (nodeId : NodeId) : EraseState :=
  if s.graph.getNode nodeId |>.isNone then s
  else
    let s := match s.rootMap.get? nodeId.id with
      | some defIdx =>
        let s := match s.graph.getNode nodeId with
          | some entry => match entry.getPort ⟨2⟩ with
            | some bodyPort =>
              if h : defIdx < s.graph.book.size then
                let d := s.graph.book[defIdx]
                { s with
                  graph := { s.graph with book := s.graph.book.set defIdx { d with root := bodyPort.node } }
                  rootMap := s.rootMap.insert bodyPort.node.id defIdx }
              else s
            | none => s
          | none => s
        { s with defWorldLams := s.defWorldLams.insert defIdx ((s.defWorldLams.getD defIdx 0) + 1) }
      | none => s
    { s with graph := applyErase s.graph nodeId .worldLam, count := s.count + 1 }

/-- Get the bypass target for a node -/
private def getBypassTarget (g : Graph) (nodeId : NodeId) (action : EraseAction) : Option NodeId :=
  match action with
  | .worldLam | .ioPairProj1 =>
    -- principal ↔ port 2 (body/record)
    (g.getNode nodeId).bind (·.getPort ⟨2⟩) |>.map (·.node)
  | .ioPairCtor =>
    -- principal ↔ port 2 (payload)
    (g.getNode nodeId).bind (·.getPort ⟨2⟩) |>.map (·.node)
  | .worldApp | .pureIO =>
    -- principal ↔ port 1 (function) for worldApp, port 2 (argument) for pureIO
    let portIdx : PortIdx := match action with | .pureIO => ⟨2⟩ | _ => ⟨1⟩
    (g.getNode nodeId).bind (·.getPort portIdx) |>.map (·.node)
  | .ioPairMat =>
    -- principal ↔ port 2 (hit branch)
    (g.getNode nodeId).bind (·.getPort ⟨2⟩) |>.map (·.node)
  | .ioBind innerAppId _ =>
    -- The outer APP stays (rewired), so no root update needed
    some nodeId
  | _ => none

/-- Process a single non-LAM target, updating definition roots if the erased node was a root -/
private def processOneOther (g : Graph) (nodeId : NodeId) (action : EraseAction)
    (rootMap : Std.HashMap Nat Nat) : Graph × Std.HashMap Nat Nat :=
  if g.getNode nodeId |>.isNone then (g, rootMap)
  else
    -- If this node is a definition root, update the root to the bypass target
    match rootMap.get? nodeId.id with
    | some defIdx =>
      match getBypassTarget g nodeId action with
      | some target =>
        match g.book[defIdx]? with
        | some d =>
          let g' := { g with book := g.book.set! defIdx { d with root := target } }
          let rm := (rootMap.erase nodeId.id).insert target.id defIdx
          (applyErase g' nodeId action, rm)
        | none => (applyErase g nodeId action, rootMap)
      | none => (applyErase g nodeId action, rootMap)
    | none => (applyErase g nodeId action, rootMap)

/-- Erase the IO type wrapper from a Value -/
private partial def eraseIOFromType (ctx : IOErasureCtx) (ty : Value) : Value :=
  match ty with
  | .vPi _ _ _ dom cod =>
    if isWorldTy ctx dom then
      -- Strip World Pi; continue to unwrap Pair underneath
      let body := applyPure cod (Value.vPrimTy .unit)
      eraseIOFromType ctx body
    else ty
  | .vSigma _ _ fst sndClos =>
    if isWorldTy ctx fst then
      applyPure sndClos fst -- Pair World a → a
    else ty
  | .vDataType _ _ =>
    if isIOPairTy ctx ty then
      match ty with
      | .vDataType _ (_ :: payload :: _) => payload
      | _ => ty
    else ty
  | _ => ty

/-- Erase all IO artifacts from the graph -/
def eraseIO (graph : Graph) (ctx : IOErasureCtx) : IO (Graph × Nat) := do
  if ctx.worldUid?.isNone && ctx.pairUid?.isNone then
    return (graph, 0)

  let targets := collectTargets graph ctx
  if targets.isEmpty then return (graph, 0)
  let rootMap := buildRootMap graph

  -- Pass 1: World LAMs 
  let mut state : EraseState := { graph, rootMap }
  for (nodeId, action) in targets do
    if let .worldLam := action then
      state := processOneWorldLam state nodeId
  let mut g := state.graph

  -- Pass 2: io_bind and pure_io (before worldApp, since io_bind APPs could also match worldApp)
  let mut rm := buildRootMap g
  for (nodeId, action) in targets do
    match action with
    | .ioBind .. | .pureIO =>
      let (g', rm') := processOneOther g nodeId action rm
      g := g'; rm := rm'
    | _ => pure ()

  -- Pass 3: remaining IO artifacts (Pair CTOR, MAT, World APP, PROJ)
  for (nodeId, action) in targets do
    match action with
    | .worldLam | .ioBind .. | .pureIO => pure ()
    | _ =>
      let (g', rm') := processOneOther g nodeId action rm
      g := g'; rm := rm'

  -- Pass 4: iterative cleanup since erasure can expose new targets
  let mut defWorldLams := state.defWorldLams
  for _ in [:8] do
    let newTargets := collectTargets g ctx
    if newTargets.isEmpty then break
    let newRootMap := buildRootMap g
    let mut newState : EraseState := { graph := g, rootMap := newRootMap }
    for (nodeId, action) in newTargets do
      if let .worldLam := action then
        newState := processOneWorldLam newState nodeId
    g := newState.graph
    for (k, v) in newState.defWorldLams.toList do
      defWorldLams := defWorldLams.insert k (v + defWorldLams.getD k 0)
    rm := buildRootMap g
    for (nodeId, action) in newTargets do
      match action with
      | .worldLam => pure ()
      | _ =>
        let (g', rm') := processOneOther g nodeId action rm
        g := g'; rm := rm'

  -- Pass 5: update definition arities
  for (k, v) in state.defWorldLams.toList do
    defWorldLams := defWorldLams.insert k (v + defWorldLams.getD k 0)
  for (defIdx, worldLams) in defWorldLams.toList do
    if let some d := g.book[defIdx]? then
      let newArity := if d.arity >= worldLams then d.arity - worldLams else 0
      g := { g with book := g.book.set! defIdx { d with arity := newArity } }
  for i in List.range g.book.size do
    if !defWorldLams.contains i then
      if let some d := g.book[i]? then
        let worldParams := countWorldParamsInType ctx d.ty
        if worldParams > 0 && d.arity >= worldParams then
          g := { g with book := g.book.set! i { d with arity := d.arity - worldParams } }

  for i in List.range g.book.size do
    if let some d := g.book[i]? then
      if d.arity == 0 then
        if let some rootEntry := g.getNode d.root then
          if let .ctor tag 2 := rootEntry.node then
            if tag == 0xFFFE then
              if let some fnPort := rootEntry.getPort ⟨1⟩ then
                -- The function pointer may be a REF/ALO to another definition.
                -- Follow it to the actual body root.
                -- Follow REF/ALO to target definition's root
                let fnNode := g.getNode fnPort.node
                let refTarget := fnNode.bind fun e => match e.node with
                  | .ref refId | .alo refId => g.book[refId]?.map (·.root)
                  | _ => none
                let actualRoot := refTarget.getD fnPort.node
                IO.eprintln s!"[IOErasure 5c] def[{i}] '{d.name.display}' root={d.root.id} -> {actualRoot.id}"
                g := { g with book := g.book.set! i { d with root := actualRoot } }

  -- Pass 6: update definition types
  let mut newBook := g.book
  for i in List.range g.book.size do
    if let some d := g.book[i]? then
      let newTy := eraseIOFromType ctx d.ty
      newBook := newBook.set! i { d with ty := newTy }
  g := { g with book := newBook }

  return (g, state.count)

end Somac.Circuit.IOErasure
