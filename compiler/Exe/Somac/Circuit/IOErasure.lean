import Somac.Circuit.Graph
import Somac.Circuit.Node
import Somac.Circuit.Lower
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
  abbrevEnv : Soma.Dependent.AbbrevEnv := {}
  deriving Inhabited

private def isWorldTy (ctx : IOErasureCtx) (v : Value) : Bool :=
  let v := Somac.Circuit.Lower.unfoldValue v ctx.abbrevEnv
  match v with
  | .vPrimTy .world => true
  | .vDataType uid _ => ctx.worldUid?.any (· == uid.id)
  | _ => false

/-- Unfold type aliases with a depth limit to prevent infinite recursion -/
private def safeUnfold (ty : Value) (env : Soma.Dependent.AbbrevEnv) (fuel : Nat := 5) : Value :=
  match fuel with
  | 0 => ty
  | fuel + 1 =>
    let ty' := Somac.Circuit.Lower.unfoldValue ty env
    match ty' with
    | .vDataType _ _ => safeUnfold ty' env fuel
    | _ => ty'

private def isIOPairTy (ctx : IOErasureCtx) (v : Value) : Bool :=
  let v := safeUnfold v ctx.abbrevEnv
  match v with
  | .vSigma _ _ fst _ => isWorldTy ctx fst
  | .vDataType uid params =>
    ctx.pairUid?.any (· == uid.id) && match params with
      | fst :: _ :: _ => isWorldTy ctx fst
      | _ => false
  | _ => false

private def hasWorldDomain (ctx : IOErasureCtx) (ty : Value) : Bool :=
  let ty := safeUnfold ty ctx.abbrevEnv
  match ty.piDomain? with
  | some dom => isWorldTy ctx dom
  | none => false

/-- Count explicit World parameters in a function type (unfolds type aliases) -/
private def countWorldParamsInType (ctx : IOErasureCtx) (ty : Value) (fuel : Nat := 20) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 =>
    let ty := safeUnfold ty ctx.abbrevEnv
    match ty with
    | .vPi _ binder _ dom cod =>
      if binder.isImplicit && dom.isType then
        countWorldParamsInType ctx (applyPure cod (Value.vNeutral dom (.nVar ⟨"_", ⟨0⟩⟩))) fuel
      else if isWorldTy ctx dom then
        1 + countWorldParamsInType ctx (applyPure cod (Value.vPrimTy .unit)) fuel
      else
        countWorldParamsInType ctx (applyPure cod (Value.vNeutral dom (.nVar ⟨"_", ⟨0⟩⟩))) fuel
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
  | ioPairCtor  -- bypass CTOR to payload (port 2), ERA World field (port 1), remove CTOR
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

/-- Resolve through REF/ALO indirections to a definition's root node -/
private def resolveToRoot (g : Graph) (nodeId : NodeId) : NodeId :=
  match g.getNode nodeId with
  | some entry => match entry.node with
    | .ref refId | .alo refId => match g.book[refId]? with
      | some def_ => def_.root
      | none => nodeId
    | _ => nodeId
  | none => nodeId

/-- Walk a LAM chain from `start`, matching each LAM's position against the Pi
    domains from `ty` -/
private def findWorldLamVars (g : Graph) (ctx : IOErasureCtx)
    (start : NodeId) (ty : Value) : Array Nat := Id.run do
  let mut result : Array Nat := #[]
  let mut current := start
  let mut piTy := safeUnfold ty ctx.abbrevEnv
  for _ in [:30] do
    piTy := safeUnfold piTy ctx.abbrevEnv
    match piTy with
    | .vPi _ binder _ dom cod =>
      if binder.isImplicit && dom.isType then
        piTy := applyPure cod (Value.vNeutral dom (.nVar ⟨"_", ⟨0⟩⟩))
      else
        if let some entry := g.getNode current then
          if let .lam _ := entry.node then
            if isWorldTy ctx dom then
              if let some varPort := entry.getPort ⟨1⟩ then
                result := result.push varPort.node.id
            if let some bodyPort := entry.getPort ⟨2⟩ then
              current := bodyPort.node
            else break
          else break
        else break
        piTy := applyPure cod (Value.vNeutral dom (.nVar ⟨"_", ⟨0⟩⟩))
    | _ => break
  result

/-- Unwrap a definition root through closure CTOR(0xFFFE,2) and REF indirections to find the actual LAM chain start -/
private def unwrapToLamChain (g : Graph) (root : NodeId) : NodeId := Id.run do
  let mut current := root
  for _ in [:3] do
    if let some entry := g.getNode current then
      match entry.node with
      | .ctor tag 2 =>
        if tag == 0xFFFE then
          if let some fnPort := entry.getPort ⟨1⟩ then
            current := resolveToRoot g fnPort.node
          else break
        else break
      | .ref _ | .alo _ =>
        current := resolveToRoot g current
      | _ => break
    else break
  current

/-- Trace all nodes that carry World tokens through the graph -/
private def traceWorldFlow (g : Graph) (ctx : IOErasureCtx) : IO (Std.HashSet Nat) := do
  let mut world : Std.HashSet Nat := {}

  -- Seed 1: nodes with explicit World type
  for (nodeId, _) in g.nodes.toList do
    if let some entry := g.getNode ⟨nodeId⟩ then
      if isWorldTy ctx entry.ty then
        world := world.insert nodeId

  -- Seed 2: definition type analysis
  for def_ in g.book do
    let wp := countWorldParamsInType ctx def_.ty
    if wp > 0 then
      let lamStart := unwrapToLamChain g def_.root
      let vars := findWorldLamVars g ctx lamStart def_.ty
      for wId in vars do
        world := world.insert wId

  -- Seed 3: LAM nodes with World domain
  for (nodeId, _) in g.nodes.toList do
    if let some entry := g.getNode ⟨nodeId⟩ then
      if let .lam _ := entry.node then
        if hasWorldDomain ctx entry.ty then
          if let some varPort := entry.getPort ⟨1⟩ then
            world := world.insert varPort.node.id

  -- Seed 4: IO Pair-typed nodes (concrete annotation)
  for (nodeId, _) in g.nodes.toList do
    if let some entry := g.getNode ⟨nodeId⟩ then
      if isIOPairTy ctx entry.ty then
        world := world.insert nodeId

  -- Propagate: follow World data flow (fixed-point)
  -- World flows: variable → APP arg, CTOR field, PROJ 0 output → next APP arg
  for _ in [:20] do
    let prevSize := world.size
    for wId in world.toList do
      if let some entry := g.getNode ⟨wId⟩ then
        if let some target := entry.getPrincipal then
          if let some targetEntry := g.getNode target.node then
            match targetEntry.node with
            | .ctor 0 2 => -- World → CTOR field 1: marks CTOR as IO Pair
              if target.port == ⟨1⟩ then world := world.insert target.node.id
            | .app => -- World → APP port 2: marks APP as World application
              if target.port == ⟨2⟩ then world := world.insert target.node.id
            | .dup _ => -- World → DUP: both DUP outputs carry World
              world := world.insert target.node.id
            | _ => pure ()
        if let .ctor 0 2 := entry.node then
          if let some consumer := entry.getPrincipal then
            world := world.insert consumer.node.id
            -- Trace through MAT → hit LAM → variable → PROJ 0
            if let some cEntry := g.getNode consumer.node then
              if let .mat _ := cEntry.node then
                if let some hitPort := cEntry.getPort ⟨2⟩ then
                  if let some hitEntry := g.getNode hitPort.node then
                    if let .lam _ := hitEntry.node then
                      if let some varPort := hitEntry.getPort ⟨1⟩ then
                        -- The variable receives the Pair; mark it
                        world := world.insert varPort.node.id
                        -- Check if anything does PROJ 0 on it
                        if let some varEntry := g.getNode varPort.node then
                          if let some varConsumer := varEntry.getPrincipal then
                            if let some vcEntry := g.getNode varConsumer.node then
                              if let .proj 0 := vcEntry.node then
                                world := world.insert varConsumer.node.id
    if world.size == prevSize then break
  pure world

/-- Classify a node for IO erasure using World-flow analysis -/
private def classifyNode (g : Graph) (nodeId : NodeId) (ctx : IOErasureCtx)
    (worldNodes : Std.HashSet Nat := {})
    : Option EraseAction := do
  let entry ← g.getNode nodeId
  match entry.node with
  | .lam _ =>
    if hasWorldDomain ctx entry.ty then some .worldLam else none
  | .ctor tag arity =>
    if tag == 0 && arity == 2 then
      -- IO Pair CTOR: detected by type OR by World-flow (first field is World-carrying)
      let typeCheck := isIOPairTy ctx entry.ty
      let flowCheck := worldNodes.contains nodeId.id
      let fstPortCheck := match entry.getPort ⟨1⟩ with
        | some fstPort => Id.run do
          let mut cur := fstPort.node
          for _ in [:10] do
            if worldNodes.contains cur.id then return true
            match g.getNode cur with
            | some curEntry =>
              if isWorldTy ctx curEntry.ty then return true
              match curEntry.node with
              | .dup _ =>
                -- DUP relays its input: follow principal port (the original value source)
                match curEntry.getPrincipal with
                | some p => cur := p.node
                | none => break
              | .lam _ =>
                -- LAM: check if the domain (parameter type) is World
                if hasWorldDomain ctx curEntry.ty then return true
                break
              | .use =>
                -- USE relays port 1 as sequentializer
                match curEntry.getPort ⟨1⟩ with
                | some p => cur := p.node
                | none => break
              | _ => break
            | none => break
          return false
        | none => false
      let isIO := typeCheck || flowCheck || fstPortCheck
      if isIO then some .ioPairCtor else none
    else none
  | .mat _ =>
    -- IO Pair MAT: scrutinee is an IO Pair (by type, by World-flow or by structure)
    let scrutPortNode := entry.getPort ⟨1⟩ |>.map (·.node)
    let scrutTy := scrutPortNode.bind (g.getNode ·) |>.map (·.ty) |>.getD entry.ty
    let isIO := isIOPairTy ctx scrutTy || isIOPairTy ctx entry.ty ||
      scrutPortNode.any (worldNodes.contains ·.id)
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
    -- World APP: detected by type OR by World-flow (argument is World-carrying)
    let fnExpectsWorld := match entry.getPort ⟨1⟩ with
      | some fnPort => match g.getNode fnPort.node with
        | some fnEntry => hasWorldDomain ctx fnEntry.ty
        | none => false
      | none => false
    let argIsWorld := match entry.getPort ⟨2⟩ with
      | some argPort =>
        worldNodes.contains argPort.node.id ||
        match g.getNode argPort.node with
        | some argEntry => isWorldTy ctx argEntry.ty
        | none => false
      | none => false
    if fnExpectsWorld || argIsWorld || worldNodes.contains nodeId.id then some .worldApp else none
  | .proj fieldIdx =>
    let recPort := entry.getPort ⟨1⟩
    let recordTy := match recPort with
      | some rp => match g.getNode rp.node with
        | some recEntry => recEntry.ty
        | none => entry.ty
      | none => entry.ty
    -- IO Pair PROJ: record is IO Pair by type or by World-flow
    let recIsIOPair := isIOPairTy ctx recordTy ||
      recPort.any (fun rp => worldNodes.contains rp.node.id)
    if recIsIOPair then
      if fieldIdx == 0 then some .ioPairProj0
      else if fieldIdx == 1 then some .ioPairProj1
      else none
    else none
  | _ => none

/-- Erase the IO type wrapper from a Value (unfolds type aliases first).
    Only strips the outermost IO wrapper — used for individual node types. -/
private def eraseIOFromType (ctx : IOErasureCtx) (ty : Value) (fuel : Nat := 10) : Value :=
  match fuel with
  | 0 => ty
  | fuel + 1 =>
  let ty := safeUnfold ty ctx.abbrevEnv
  match ty with
  | .vPi _ _ _ dom cod =>
    if isWorldTy ctx dom then
      let body := applyPure cod (Value.vPrimTy .unit)
      eraseIOFromType ctx body fuel
    else ty
  | .vSigma _ _ fst sndClos =>
    if isWorldTy ctx fst then
      applyPure sndClos fst
    else ty
  | .vDataType _ _ =>
    if isIOPairTy ctx ty then
      match ty with
      | .vDataType _ (_ :: payload :: _) => payload
      | _ => ty
    else ty
  | _ => ty

/-- Erase IO from an entire function type: recursively walk all Pi binders,
    remove World parameters, and unwrap `Pair World a` in the return position.
    Reconstructs the type bottom-up with `Closure.const` so downstream passes
    (Alloy lowering, signature building) see the post-erasure type directly.

    Example: `A -> B -> World -> Pair World C` becomes `A -> B -> C`. -/
partial def eraseIOFromFuncType (ctx : IOErasureCtx) (ty : Value) : Value :=
  let ty := safeUnfold ty ctx.abbrevEnv
  match ty with
  | .vPi qty binder name dom cod =>
    if binder.isImplicit && dom.isType then
      -- Preserve implicit type parameters, recurse into codomain.
      -- Use neutral for type params (they affect downstream type computation).
      let body := applyPure cod (Value.vNeutral dom (.nVar ⟨name, ⟨0⟩⟩))
      let erasedBody := eraseIOFromFuncType ctx body
      .vPi qty binder name dom (.const name erasedBody)
    else if isWorldTy ctx dom then
      -- Drop the World parameter entirely, recurse into codomain.
      -- Pass World so IO Pair construction retains World as first field.
      let body := applyPure cod (Value.vPrimTy .world)
      eraseIOFromFuncType ctx body
    else
      -- Preserve non-World parameter, recurse into codomain
      let neutralArg := Value.vNeutral dom (.nVar ⟨name, ⟨0⟩⟩)
      let body := applyPure cod neutralArg
      let erasedBody := eraseIOFromFuncType ctx body
      .vPi qty binder name dom (.const name erasedBody)
  -- At the return position: unwrap IO Pair types
  | .vSigma _ _ fst sndClos =>
    if isWorldTy ctx fst then applyPure sndClos fst
    else ty
  | .vDataType uid params =>
    if isIOPairTy ctx ty then
      match ty with
      | .vDataType _ (_ :: payload :: _) => payload
      | _ => ty
    else
      ty
  | _ => ty

/-- Apply a single erasure action to the graph -/
private def applyErase (g : Graph) (nodeId : NodeId) (action : EraseAction) (ctx : IOErasureCtx)
    : Graph := Id.run do
  let some entry := g.getNode nodeId | return g
  let mut graph := g
  match action with
  | .worldLam =>
    if let some varPort := entry.getPort ⟨1⟩ then
      graph := graph.disconnect ⟨nodeId, ⟨1⟩⟩
      graph := addEra graph varPort
    graph := link graph (PortId.principal nodeId) ⟨nodeId, ⟨2⟩⟩
    graph := graph.removeNode nodeId

  | .ioPairMat | .ioPairProj1 =>
    pure ()

  | .worldApp =>
    graph := link graph (PortId.principal nodeId) ⟨nodeId, ⟨1⟩⟩
    if let some argPort := entry.getPort ⟨2⟩ then
      graph := graph.disconnect ⟨nodeId, ⟨2⟩⟩
      graph := addEra graph argPort
    graph := graph.removeNode nodeId

  | .ioPairCtor =>
    -- Erase IO Pair CTOR. Strategy depends on consumer:
    -- - MAT consumer: replace CTOR with USE node (preserves MAT interaction)
    -- - Other consumer: bypass CTOR to payload, ERA World field
    let consumerIsMat := match entry.getPrincipal with
      | some consumer => match graph.getNode consumer.node with
        | some cEntry => match cEntry.node with | .mat _ => true | _ => false
        | none => false
      | none => false
    if consumerIsMat then
      -- Replace with USE(world, payload)
      let (useId, graph') := graph.addNode .use entry.ty
      graph := graph'
      if let some worldPort := entry.getPort ⟨1⟩ then
        graph := graph.disconnect ⟨nodeId, ⟨1⟩⟩
        graph := graph.connect ⟨useId, ⟨1⟩⟩ worldPort
      if let some payloadPort := entry.getPort ⟨2⟩ then
        graph := graph.disconnect ⟨nodeId, ⟨2⟩⟩
        graph := graph.connect ⟨useId, ⟨2⟩⟩ payloadPort
      if let some consumer := entry.getPrincipal then
        graph := graph.disconnect (PortId.principal nodeId)
        graph := graph.connect (PortId.principal useId) consumer
      graph := graph.removeNode nodeId
    else
      -- Bypass to payload, ERA World
      graph := link graph (PortId.principal nodeId) ⟨nodeId, ⟨2⟩⟩
      if let some worldPort := entry.getPort ⟨1⟩ then
        graph := graph.disconnect ⟨nodeId, ⟨1⟩⟩
        graph := addEra graph worldPort
      graph := graph.removeNode nodeId

  | .ioPairProj0 =>
    -- Insert USE AFTER PROJ 0: forces the IO action, produces unit.
    let (useId, graph') := graph.addNode .use (Value.vPrimTy .unit)
    graph := graph'
    let (unitId, graph') := graph.addNode (.num .u64 0) (Value.vPrimTy .unit)
    graph := graph'
    graph := graph.connect ⟨useId, ⟨2⟩⟩ (PortId.principal unitId)
    if let some consumer := entry.getPrincipal then
      graph := graph.disconnect (PortId.principal nodeId)
      graph := graph.connect (PortId.principal nodeId) ⟨useId, ⟨1⟩⟩
      graph := graph.connect (PortId.principal useId) consumer
    else
      graph := graph.connect (PortId.principal nodeId) ⟨useId, ⟨1⟩⟩

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

    -- io_bind m f → APP(f, m): apply continuation to the IO action result
    -- Reconnect: APP₂.function = f, APP₂.argument = m
    if let some ft := fTarget then
      graph := graph.connect ⟨nodeId, ⟨1⟩⟩ ft
    if let some mt := mTarget then
      graph := graph.connect ⟨nodeId, ⟨2⟩⟩ mt

    -- Remove the inner APP₁
    graph := graph.removeNode innerAppId

    -- ERA the REF/ALO node for io_bind
    if let some rt := refTarget then
      graph := addEra graph rt

  graph

/-- Classify all nodes and collect erasure targets -/
private def collectTargets (graph : Graph) (ctx : IOErasureCtx)
    : IO (Array (NodeId × EraseAction)) := do
  let worldNodes ← traceWorldFlow graph ctx
  pure <| graph.nodes.fold (init := #[]) fun acc id _ =>
    match classifyNode graph ⟨id⟩ ctx worldNodes with
    | some action => acc.push (⟨id⟩, action)
    | none => acc

/-- Build definition root → index map -/
private def buildRootMap (graph : Graph) : Std.HashMap Nat Nat :=
  (List.range graph.book.size).foldl (init := {}) fun acc i =>
    match graph.book[i]? with
    | some def_ => acc.insert def_.root.id i
    | none => acc

/-- Build a map from every node in each definition's root LAM chain to the definition index -/
private def buildLamChainMap (graph : Graph) : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := {}
  for i in List.range graph.book.size do
    if let some def_ := graph.book[i]? then
      let mut cur := def_.root
      for _ in [:30] do
        if m.contains cur.id then break
        match graph.getNode cur with
        | some e => match e.node with
          | .lam _ =>
            m := m.insert cur.id i
            match e.getPort ⟨2⟩ with
            | some bp => cur := bp.node
            | none => break
          | _ => break
        | none => break
  m

/-- State threaded through the erasure passes -/
private structure EraseState where
  graph : Graph
  rootMap : Std.HashMap Nat Nat
  lamChainMap : Std.HashMap Nat Nat := {}
  count : Nat := 0
  /-- Tracks how many World LAMs were actually removed per definition -/
  defWorldLams : Std.HashMap Nat Nat := {}

/-- Process a single World LAM target -/
private def processOneWorldLam (s : EraseState) (nodeId : NodeId) (ctx : IOErasureCtx) : EraseState :=
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
      | none =>
        match s.lamChainMap.get? nodeId.id with
        | some defIdx =>
          { s with defWorldLams := s.defWorldLams.insert defIdx ((s.defWorldLams.getD defIdx 0) + 1) }
        | none => s
    { s with graph := applyErase s.graph nodeId .worldLam ctx, count := s.count + 1 }

/-- Get the bypass target for a node -/
private def getBypassTarget (g : Graph) (nodeId : NodeId) (action : EraseAction) : Option NodeId :=
  match action with
  | .worldLam | .ioPairMat | .ioPairProj1 =>
    some nodeId -- no-ops: bypass target is self
  | .worldApp =>
    -- worldApp bypasses to function (port 1), dropping World argument
    (g.getNode nodeId).bind (·.getPort ⟨1⟩) |>.map (·.node)
  | .pureIO =>
    (g.getNode nodeId).bind (·.getPort ⟨2⟩) |>.map (·.node)
  | .ioPairCtor =>
    -- CTOR bypassed to payload and the payload node becomes the new root
    (g.getNode nodeId).bind (·.getPort ⟨2⟩) |>.map (·.node)
  | .ioPairProj0 =>
    none
  | .ioBind .. =>
    some nodeId -- outer APP stays (rewired to APP(f, m))

/-- Process a single non-LAM target, updating definition roots if the erased node was a root -/
private def processOneOther (g : Graph) (nodeId : NodeId) (action : EraseAction)
    (rootMap : Std.HashMap Nat Nat) (ctx : IOErasureCtx) : Graph × Std.HashMap Nat Nat :=
  if g.getNode nodeId |>.isNone then (g, rootMap)
  else
    match rootMap.get? nodeId.id with
    | some defIdx =>
      match getBypassTarget g nodeId action with
      | some target =>
        match g.book[defIdx]? with
        | some d =>
          let g' := { g with book := g.book.set! defIdx { d with root := target } }
          let rm := (rootMap.erase nodeId.id).insert target.id defIdx
          (applyErase g' nodeId action ctx, rm)
        | none => (applyErase g nodeId action ctx, rootMap)
      | none => (applyErase g nodeId action ctx, rootMap)
    | none => (applyErase g nodeId action ctx, rootMap)

/-- Collapse type-argument APPs (APP(X, ERA) → X) in chains leading to
    io_bind/pure_io REFs -/
private def collapseTypeArgApps (g : Graph) (ctx : IOErasureCtx) : Graph := Id.run do
  let ioBookIndices : Std.HashSet Nat := Id.run do
    let mut s : Std.HashSet Nat := {}
    if let some idx := ctx.ioBindBookIdx? then s := s.insert idx
    if let some idx := ctx.pureIOBookIdx? then s := s.insert idx
    s
  if ioBookIndices.isEmpty then return g
  let mut graph := g
  let mut collapseTargets : Array NodeId := #[]
  for (nid, _) in graph.nodes.toList do
    if let some entry := graph.getNode ⟨nid⟩ then
      if let .app := entry.node then
        let argIsEra := match entry.getPort ⟨2⟩ with
          | some argPort => match graph.getNode argPort.node with
            | some argEntry => match argEntry.node with | .era => true | _ => false
            | none => false
          | none => false
        if argIsEra then
          -- Walk the function chain to see if it reaches an io_bind/pure_io REF
          let mut current := entry.getPort ⟨1⟩
          let mut reachesIORef := false
          for _ in [:20] do
            match current with
            | some port =>
              match graph.getNode port.node with
              | some fnEntry =>
                match fnEntry.node with
                | .ref idx | .alo idx =>
                  if ioBookIndices.contains idx then reachesIORef := true
                  current := none
                | .app =>
                  let innerArgIsEra := match fnEntry.getPort ⟨2⟩ with
                    | some ap => match graph.getNode ap.node with
                      | some ae => match ae.node with | .era => true | _ => false
                      | none => false
                    | none => false
                  if innerArgIsEra then current := fnEntry.getPort ⟨1⟩
                  else current := none
                | _ => current := none
              | none => current := none
            | none => break
          if reachesIORef then
            collapseTargets := collapseTargets.push ⟨nid⟩
  for appId in collapseTargets do
    if let some appEntry := graph.getNode appId then
      graph := link graph (PortId.principal appId) ⟨appId, ⟨1⟩⟩
      if let some argPort := appEntry.getPort ⟨2⟩ then
        graph := graph.disconnect ⟨appId, ⟨2⟩⟩
        graph := addEra graph argPort
      graph := graph.removeNode appId
  graph


/-- Erase all IO artifacts from the graph -/
def eraseIO (graph : Graph) (ctx : IOErasureCtx) : IO (Graph × Nat) := do
  if ctx.worldUid?.isNone && ctx.pairUid?.isNone then
    return (graph, 0)

  let targets ← collectTargets graph ctx
  if targets.isEmpty then return (graph, 0)
  let rootMap := buildRootMap graph

  -- Pass 1: World LAMs
  let lamChainMap := buildLamChainMap graph
  let mut state : EraseState := { graph, rootMap, lamChainMap }
  for (nodeId, action) in targets do
    if let .worldLam := action then
      state := processOneWorldLam state nodeId ctx
  let mut g := state.graph
  let mut worldLamCounts := state.defWorldLams

  -- Pass 2: Collapse type-argument APPs on io_bind/pure_io chains
  g := collapseTypeArgApps g ctx
  -- Re-collect targets after type-arg collapse
  let targets ← collectTargets g ctx

  -- Build a set of node IDs belonging to the io_bind/pure_io definitions
  let ioDefNodes : Std.HashSet Nat := Id.run do
    let mut nodes : Std.HashSet Nat := {}
    let defsToSkip := #[ctx.ioBindBookIdx?, ctx.pureIOBookIdx?].filterMap id
    for bookIdx in defsToSkip do
      if let some def_ := g.book[bookIdx]? then
        let mut queue : Array Somac.Circuit.Node.NodeId := #[def_.root]
        for _ in [:500] do
          if queue.isEmpty then break
          let nid := queue.back!
          queue := queue.pop
          if nodes.contains nid.id then continue
          nodes := nodes.insert nid.id
          if let some entry := g.getNode nid then
            for pi in [:entry.node.numPorts] do
              if let some port := entry.getPort ⟨pi⟩ then
                if !nodes.contains port.node.id then
                  queue := queue.push port.node
    nodes

  -- Pass 3: io_bind and pure_io (before worldApp, since io_bind APPs could also match worldApp)
  let mut rm := buildRootMap g
  for (nodeId, action) in targets do
    match action with
    | .ioBind .. | .pureIO =>
      -- Skip targets inside io_bind/pure_io definitions
      if ioDefNodes.contains nodeId.id then pure ()
      else
        let (g', rm') := processOneOther g nodeId action rm ctx
        g := g'; rm := rm'
    | _ => pure ()

  -- Pass 4: remaining IO artifacts (Pair CTOR, MAT, PROJ)
  for (nodeId, action) in targets do
    match action with
    | .worldLam | .worldApp | .ioBind .. | .pureIO => pure ()
    | _ =>
      let (g', rm') := processOneOther g nodeId action rm ctx
      g := g'; rm := rm'

  -- Pass 5: iterative cleanup because erasure exposes new targets
  let mut processedNodes : Std.HashSet Nat := {}
  -- Mark all initially-processed nodes to avoid re-detecting no-op targets
  for (nodeId, _) in targets do
    processedNodes := processedNodes.insert nodeId.id
  for _iter in [:8] do
    let newTargets ← collectTargets g ctx
    -- Filter out already-processed nodes (no-op actions are re-detected every iteration)
    let freshTargets := newTargets.filter fun (nodeId, _) => !processedNodes.contains nodeId.id
    if freshTargets.isEmpty then break
    for (nodeId, _) in freshTargets do
      processedNodes := processedNodes.insert nodeId.id
    let newRootMap := buildRootMap g
    let newLamChainMap := buildLamChainMap g
    let mut newState : EraseState := { graph := g, rootMap := newRootMap, lamChainMap := newLamChainMap }
    for (nodeId, action) in freshTargets do
      if let .worldLam := action then
        newState := processOneWorldLam newState nodeId ctx
    g := newState.graph
    -- Merge World LAM counts from iterative cleanup
    for (defIdx, count) in newState.defWorldLams.toList do
      worldLamCounts := worldLamCounts.insert defIdx ((worldLamCounts.getD defIdx 0) + count)
    rm := buildRootMap g
    for (nodeId, action) in freshTargets do
      match action with
      | .worldLam | .worldApp => pure ()
      | _ =>
        let (g', rm') := processOneOther g nodeId action rm ctx
        g := g'; rm := rm'

  -- Track definitions whose closure roots were bypassed (ERA env)
  let mut closureBypassed : Std.HashSet Nat := {}

  -- Pass 6a: erase IO Pair CTORs inside closure environments
  for (nodeId, _) in g.nodes.toList do
    if let some entry := g.getNode ⟨nodeId⟩ then
      if let .ctor tag 2 := entry.node then
        if tag == 0xFFFE then
          -- Check if environment (port 2) is a Pair CTOR(0, 2) with IO Pair type
          if let some envPort := entry.getPort ⟨2⟩ then
            if let some envEntry := g.getNode envPort.node then
              if let .ctor 0 2 := envEntry.node then
                let envIsIO := isIOPairTy ctx envEntry.ty
                if envIsIO then
                  -- This is a specialized IO Pair in a closure env. Bypass it
                  -- to its payload (port 2), ERA the World field (port 1).
                  let pairId := envPort.node
                  -- Use link to bypass Pair: closure.env ↔ Pair.payload
                  g := link g (PortId.mk ⟨nodeId⟩ ⟨2⟩) (PortId.mk pairId ⟨2⟩)
                  if let some worldPort := envEntry.getPort ⟨1⟩ then
                    g := g.disconnect (PortId.mk pairId ⟨1⟩)
                    g := addEra g worldPort
                  g := g.removeNode pairId

  -- Pass 6b: fix closure CTOR roots after IO erasure
  for i in List.range g.book.size do
    if let some d := g.book[i]? then
      if let some rootEntry := g.getNode d.root then
        if let .ctor tag 2 := rootEntry.node then
          if tag == 0xFFFE then
            -- Check if environment (port 2) is ERA
            let envIsEra := match rootEntry.getPort ⟨2⟩ with
              | some envPort =>
                match g.getNode envPort.node with
                | some envEntry => match envEntry.node with | .era => true | _ => false
                | none => true
              | none => true
            if envIsEra then
              -- Environment was erased (World captured value removed by IO erasure)
              if let some fnPort := rootEntry.getPort ⟨1⟩ then
                -- Follow REF/ALO to find the inner function's book index
                let innerDefIdx? := match g.getNode fnPort.node with
                  | some fnEntry => match fnEntry.node with
                    | .ref idx | .alo idx => some idx
                    | _ =>
                      -- LAM node: find which definition it belongs to
                      Id.run do
                        for j in [:g.book.size] do
                          if let some dd := g.book[j]? then
                            if dd.root == fnPort.node then return some j
                        return none
                  | none => none
                match innerDefIdx? with
                | some innerIdx =>
                  if let some innerDef := g.book[innerIdx]? then
                    -- Adopt the inner function's root and arity
                    g := { g with book := g.book.set! i { d with root := innerDef.root, arity := innerDef.arity } }
                    closureBypassed := closureBypassed.insert i
                | none =>
                  -- Fallback: count inner LAMs
                  let innerRoot := resolveToRoot g fnPort.node
                  let mut lamCount : Nat := 0
                  let mut cur := innerRoot
                  for _ in [:20] do
                    if let some e := g.getNode cur then
                      if let .lam _ := e.node then
                        lamCount := lamCount + 1
                        if let some bp := e.getPort ⟨2⟩ then
                          cur := bp.node
                        else break
                      else break
                    else break
                  if lamCount < d.arity then
                    g := { g with book := g.book.set! i { d with arity := lamCount } }
            else
              -- Non-ERA environment: count inner LAMs for arity fixup
              if let some fnPort := rootEntry.getPort ⟨1⟩ then
                let innerRoot := resolveToRoot g fnPort.node
                let mut lamCount : Nat := 0
                let mut cur := innerRoot
                for _ in [:20] do
                  if let some e := g.getNode cur then
                    if let .lam _ := e.node then
                      lamCount := lamCount + 1
                      if let some bp := e.getPort ⟨2⟩ then
                        cur := bp.node
                      else break
                    else break
                  else break
                if lamCount < d.arity then
                  g := { g with book := g.book.set! i { d with arity := lamCount } }

  -- Pass 6c: erase World APPs using the ORIGINAL targets classification
  rm := buildRootMap g
  for (nodeId, action) in targets do
    if let .worldApp := action then
      if g.getNode nodeId |>.isSome then
        let (g', rm') := processOneOther g nodeId action rm ctx
        g := g'; rm := rm'

  -- Pass 6d: propagate types forward through DUP nodes
  for (nodeId, _) in g.nodes.toList do
    if let some entry := g.getNode ⟨nodeId⟩ then
      if let .dup _ := entry.node then
        if let some principalTarget := entry.getPrincipal then
          if let some sourceEntry := g.getNode principalTarget.node then
            if isWorldTy ctx entry.ty && !isWorldTy ctx sourceEntry.ty then
              g := g.updateNode ⟨nodeId⟩ fun e => { e with ty := sourceEntry.ty }

  -- Pass 7: update definition types and arities to reflect IO erasure
  for i in List.range g.book.size do
    if let some d := g.book[i]? then
      let erasedTy := eraseIOFromFuncType ctx d.ty
      -- Check if the type actually changed (IO was detected and stripped)
      let originalArity := d.ty.explicitArityFull (some (Somac.Circuit.Lower.unfoldValue · ctx.abbrevEnv))
      let erasedArity := erasedTy.explicitArityFull (some (Somac.Circuit.Lower.unfoldValue · ctx.abbrevEnv))
      let worldParams := if originalArity >= erasedArity then originalArity - erasedArity else 0
      if worldParams > 0 then
        let removedLams := if d.reducibility == .external then worldParams
          else worldLamCounts.getD i 0
        -- Guard: check if body has surviving CTOR(0,2) (closure capture Pairs)
        let bodyHasIOPair := if d.reducibility == .external then false
          else Id.run do
            let mut queue : Array NodeId := #[d.root]
            let mut visited : Std.HashSet Nat := {}
            for _ in [:200] do
              if queue.isEmpty then break
              let nodeId := queue.back!
              queue := queue.pop
              if visited.contains nodeId.id then continue
              visited := visited.insert nodeId.id
              if let some entry := g.getNode nodeId then
                if let .ctor 0 2 := entry.node then return true
                for idx in [:entry.node.numPorts] do
                  if idx > 0 then
                    if let some port := entry.getPort ⟨idx⟩ then
                      if !visited.contains port.node.id then
                        queue := queue.push port.node
            return false
        if !bodyHasIOPair then
          let newArity := if d.arity >= removedLams then d.arity - removedLams else d.arity
          g := { g with book := g.book.set! i { d with ty := erasedTy, arity := newArity } }
        else
          pure ()

  -- Pass 8: update ALL node types for post-erasure consistency
  for (nodeId, _) in g.nodes.toList do
    if let some entry := g.getNode ⟨nodeId⟩ then
      let newTy := match entry.node with
        | .ref idx | .alo idx =>
          match g.book[idx]? with
          | some d => d.ty
          | none => eraseIOFromFuncType ctx entry.ty
        | .ctor _ _ =>
          eraseIOFromFuncType ctx entry.ty
        | .dup _ => eraseIOFromFuncType ctx entry.ty
        | _ => eraseIOFromFuncType ctx entry.ty
      g := g.updateNode ⟨nodeId⟩ fun e => { e with ty := newTy }

  pure ()

  return (g, targets.size)

end Somac.Circuit.IOErasure
