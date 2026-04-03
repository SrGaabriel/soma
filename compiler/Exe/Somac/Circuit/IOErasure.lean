import Somac.Circuit.Graph
import Somac.Circuit.Node
import Soma.Core.Value
import Std.Data.HashMap
import Std.Data.HashSet

namespace Somac.Circuit.IOErasure

open Somac.Circuit.Graph (Graph NodeEntry Definition)
open Somac.Circuit.Node (Node NodeId PortId PortIdx)
open Soma.Core (Value)

/-- Configuration for IO erasure at the Circuit IR level -/
structure IOErasureCtx where
  worldUid? : Option Nat := none
  pairUid? : Option Nat := none

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

/-- What kind of erasure to apply to a node -/
private inductive EraseAction where
  | worldLam    -- bypass LAM, ERA variable port
  | ioPairCtor  -- bypass CTOR to payload, ERA World field
  | ioPairMat   -- bypass MAT principal↔hit, ERA miss
  | worldApp    -- bypass APP principal↔function, ERA argument
  | ioPairProj0 -- replace with unit constant
  | ioPairProj1 -- bypass PROJ (identity)

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
    if tag == 0 && arity == 2 && isIOPairTy ctx entry.ty then some .ioPairCtor else none
  | .mat _ =>
    let scrutTy := match entry.getPort ⟨1⟩ with
      | some scrutPort =>
        match g.getNode scrutPort.node with
        | some scrutEntry => scrutEntry.ty
        | none => entry.ty
      | none => entry.ty
    if isIOPairTy ctx scrutTy then some .ioPairMat else none
  | .app =>
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

/-- Process a single non-LAM target -/
private def processOneOther (g : Graph) (nodeId : NodeId) (action : EraseAction) : Graph :=
  if g.getNode nodeId |>.isNone then g
  else applyErase g nodeId action

/-- Adjust definition arities to account for World LAM parameters -/
def eraseWorldLamsAtRoots (_graph : Graph) (_ctx : IOErasureCtx) : IO (Graph × Nat) :=
  pure (_graph, 0)

/-- Erase remaining IO artifacts (Pair CTORs, MATs, PROJs, World APPs) -/
def eraseIO (graph : Graph) (ctx : IOErasureCtx) : IO (Graph × Nat) := do
  if ctx.worldUid?.isNone && ctx.pairUid?.isNone then
    return (graph, 0)
  let targets := collectTargets graph ctx
  if targets.isEmpty then return (graph, 0)
  let rootMap := buildRootMap graph
  -- Process all erasures sequentially, forcing evaluation between steps
  let mut state : EraseState := { graph, rootMap }
  let mut g := graph
  -- Pass 1: World LAMs
  for (nodeId, action) in targets do
    if let .worldLam := action then
      state := processOneWorldLam state nodeId
  g := state.graph
  -- Pass 2: other nodes (Pair CTOR, MAT, APP, PROJ)
  for (nodeId, action) in targets do
    match action with
    | .worldLam => pure ()
    | _ => g := processOneOther g nodeId action
  -- Pass 3: arities
  for (defIdx, worldLams) in state.defWorldLams.toList do
    if h : defIdx < g.book.size then
      let d := g.book[defIdx]
      let newArity := if d.arity >= worldLams then d.arity - worldLams else 0
      g := { g with book := g.book.set defIdx { d with arity := newArity } }
  return (g, state.count)

end Somac.Circuit.IOErasure
