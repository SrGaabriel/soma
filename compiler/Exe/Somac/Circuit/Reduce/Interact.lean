import Somac.Circuit.Reduce.Types
import Somac.Circuit.Graph
import Somac.Circuit.Node
import Somac.Circuit.Term
import Soma.Core.Value

namespace Somac.Circuit.Reduce

open Somac.Circuit.Graph (Graph GraphM NodeEntry Definition)
open Somac.Circuit.Node (Node NodeId PortId PortIdx Label)
open Somac.Circuit.Term (Tag Op1Code Op2Code PrimType)
open Soma.Core (Value)

/-- Compute a binary operation on two 32-bit values -/
def computeOp2 (op : Op2Code) (lhs rhs : UInt32) : Except ReduceError UInt32 :=
  match op with
  | .add => .ok (lhs + rhs)
  | .sub => .ok (lhs - rhs)
  | .mul => .ok (lhs * rhs)
  | .div => if rhs == 0 then .error .divisionByZero else .ok (lhs / rhs)
  | .mod => if rhs == 0 then .error .divisionByZero else .ok (lhs % rhs)
  | .and => .ok (lhs &&& rhs)
  | .or  => .ok (lhs ||| rhs)
  | .xor => .ok (lhs ^^^ rhs)
  | .shl => .ok (lhs <<< rhs)
  | .shr => .ok (lhs >>> rhs)
  | .eq  => .ok (if lhs == rhs then 1 else 0)
  | .ne  => .ok (if lhs != rhs then 1 else 0)
  | .lt  => .ok (if lhs < rhs then 1 else 0)
  | .le  => .ok (if lhs <= rhs then 1 else 0)
  | .gt  => .ok (if lhs > rhs then 1 else 0)
  | .ge  => .ok (if lhs >= rhs then 1 else 0)

/-- Compute a unary operation on a 32-bit value -/
def computeOp1 (op : Op1Code) (val : UInt32) : UInt32 :=
  match op with
  | .not => if val == 0 then 1 else 0
  | .neg => 0 - val

/-- Result of algebraic simplification attempt -/
inductive AlgSimplification where
  /-- Result is the other operand -/
  | identity
  /-- Result is a constant value -/
  | absorb (val : UInt32)

/-- Check if a binary operation with one concrete operand can be algebraically simplified -/
def algebraicSimplify? (op : Op2Code) (val : UInt32) (constIsLeft : Bool)
    : Option AlgSimplification :=
  match op with
  | .add => if val == 0 then some .identity else none
  | .sub => if val == 0 && !constIsLeft then some .identity else none
  | .mul =>
    if val == 0 then some (.absorb 0)
    else if val == 1 then some .identity
    else none
  | .and => if val == 0 then some (.absorb 0) else none
  | .or  => if val == 0 then some .identity else none
  | .xor => if val == 0 then some .identity else none
  | .shl => if val == 0 && !constIsLeft then some .identity else none
  | .shr => if val == 0 && !constIsLeft then some .identity else none
  | _ => none

/-- Iteratively erase everything reachable from `initialPort` through principal-port interactions -/
partial def erasePort (initialPort : PortId) : ReduceM Unit := do
  let firstTarget? ← ReduceM.getConnection initialPort
  let some firstTarget := firstTarget? | return
  ReduceM.disconnect initialPort
  let mut queue : Array PortId := #[firstTarget]
  while !queue.isEmpty do
    let peer := queue.back!
    queue := queue.pop
    if !peer.port.isPrincipal then
      -- Peer is a binder slot or consumer aux: ERA stays stuck
      let era ← ReduceM.addNode .era
      ReduceM.connect (PortId.principal era) peer
    else
      -- Active pair ERA-X: fire X-specific erase by severing each aux port from its own peer
      let entry ← ReduceM.getNode peer.node
      let arity := entry.node.numAuxPorts
      match entry.node with
      | .lam erased =>
        if arity > 0 then ReduceM.modifyStats (·.incEraPropagation)
        if erased then
          ReduceM.disconnect ⟨peer.node, ⟨1⟩⟩
        else
          match ← ReduceM.getConnection ⟨peer.node, ⟨1⟩⟩ with
          | some auxPeer =>
            ReduceM.disconnect ⟨peer.node, ⟨1⟩⟩
            queue := queue.push auxPeer
          | none => pure ()
        match ← ReduceM.getConnection ⟨peer.node, ⟨2⟩⟩ with
        | some auxPeer =>
          ReduceM.disconnect ⟨peer.node, ⟨2⟩⟩
          queue := queue.push auxPeer
        | none => pure ()
      | _ =>
        if arity > 0 then ReduceM.modifyStats (·.incEraPropagation)
        for i in [:arity] do
          match ← ReduceM.getConnection ⟨peer.node, ⟨i + 1⟩⟩ with
          | some auxPeer =>
            ReduceM.disconnect ⟨peer.node, ⟨i + 1⟩⟩
            queue := queue.push auxPeer
          | none => pure ()
      ReduceM.removeNode peer.node

/-- Deep-copy a definition's subgraph, returning the principal port of the copy's root -/
partial def copySubgraph (rootId : NodeId) : ReduceM PortId := do
  let g ← ReduceM.getGraph
  let reachable := g.reachableFrom (PortId.principal rootId)

  -- Phase 1: Create fresh copies of all nodes, building ID and label maps
  let mut idMap : Std.HashMap Nat NodeId := {}
  let mut labelMap : Std.HashMap UInt32 Label := {}

  for oldId in reachable do
    match g.getNode oldId with
    | some entry =>
      let newNode ← match entry.node with
        | .dup label =>
          match labelMap.get? label.id with
          | some newLabel => pure (Node.dup newLabel)
          | none =>
            let newLabel ← ReduceM.freshLabel
            labelMap := labelMap.insert label.id newLabel
            pure (Node.dup newLabel)
        | .sup label =>
          match labelMap.get? label.id with
          | some newLabel => pure (Node.sup newLabel)
          | none =>
            let newLabel ← ReduceM.freshLabel
            labelMap := labelMap.insert label.id newLabel
            pure (Node.sup newLabel)
        | other => pure other
      let newId ← ReduceM.addNode newNode entry.ty
      -- Carry intrinsic resolved type args onto the copy so polymorphic call/reference heads stay specializable after instantiation/duplication
      if !entry.typeArgs.isEmpty then
        ReduceM.modifyGraph (·.setResolvedTypeArgs newId entry.typeArgs)
      idMap := idMap.insert oldId.id newId
    | none => pure ()

  -- Phase 2: Rewire all connections in the copy
  -- We need to re-read the graph since addNode modified it
  let g ← ReduceM.getGraph
  for oldId in reachable do
    match g.getNode oldId with
    | some entry =>
      for (pIdx, target) in entry.connections do
        match idMap.get? oldId.id with
        | some newSrc =>
          match idMap.get? target.node.id with
          | some newDst =>
            -- Both endpoints are inside the copy: wire the copies together
            if oldId.id < target.node.id ||
               (oldId.id == target.node.id && pIdx.idx < target.port.idx) then
              ReduceM.connect ⟨newSrc, pIdx⟩ ⟨newDst, target.port⟩
          | none =>
            -- Target is outside the copy: connect the copy to the external node
            ReduceM.connect ⟨newSrc, pIdx⟩ target
        | none => pure ()
    | none => pure ()

  match idMap.get? rootId.id with
  | some newRoot => pure (PortId.principal newRoot)
  | none => throw (.malformedGraph s!"root {rootId} not in reachable set during instantiation")

/-- One step of the iterative WHNF driver's control flow. -/
inductive StepResult where
  /-- A WHNF value has been reached for the current demand -/
  | done (nid : NodeId)
  /-- Continue reducing at this new demand port without pushing a frame -/
  | demand (port : PortId)
  /-- Push this frame onto the resumption stack and reduce toward the given port next -/
  | demandFrame (frame : WhnfFrame) (port : PortId)

mutual

/-- Classify a node reached at its principal port during WHNF -/
partial def stepAtPrincipal (nid : NodeId) (entry : NodeEntry) (demandPort : PortId)
    : ReduceM StepResult := do
  match entry.node with
  -- Value nodes: already in WHNF
  | .num _ _ | .num64 _ _ _ | .lam _ | .ctor _ _ | .record _ | .string | .array _
  | .sup _ | .slice | .era =>
    return .done nid

  | .app =>
    ReduceM.consumeFuel
    return .demandFrame (WhnfFrame.appFun nid entry.ty demandPort) ⟨nid, ⟨1⟩⟩

  | .op2 op =>
    ReduceM.consumeFuel
    return .demandFrame (WhnfFrame.op2Left nid op entry.ty demandPort) ⟨nid, ⟨1⟩⟩

  | .op1 op =>
    ReduceM.consumeFuel
    return .demandFrame (WhnfFrame.op1Operand nid op entry.ty demandPort) ⟨nid, ⟨1⟩⟩

  | .mat expectedTag =>
    ReduceM.consumeFuel
    return .demandFrame (WhnfFrame.matScrutinee nid expectedTag entry.ty demandPort) ⟨nid, ⟨1⟩⟩

  | .proj fieldIdx =>
    ReduceM.consumeFuel
    return .demandFrame (WhnfFrame.projRecord nid fieldIdx entry.ty demandPort) ⟨nid, ⟨1⟩⟩

  | .use =>
    ReduceM.consumeFuel
    return .demandFrame (WhnfFrame.useTerm nid demandPort) ⟨nid, ⟨1⟩⟩

  | .alo refId =>
    ReduceM.consumeFuel
    let def_ ← ReduceM.getDefinition refId
    if def_.reducibility != .reducible then
      return .done nid
    else if (← ReduceM.isNormalizingDef refId) then
      return .done nid
    else
      ReduceM.modifyStats (·.incInstantiation)
      let rootCopy ← copySubgraph def_.root
      let aloConsumer ← ReduceM.getConnection (PortId.principal nid)
      ReduceM.disconnect (PortId.principal nid)
      match aloConsumer with
      | some consumer => ReduceM.connect consumer rootCopy
      | none => pure ()
      ReduceM.removeNode nid
      ReduceM.trackPeakNodes
      ReduceM.addNormalizingDef refId
      return .demand demandPort

  | .ref refId =>
    ReduceM.consumeFuel
    let def_ ← ReduceM.getDefinition refId
    if def_.reducibility != .reducible then
      return .done nid
    else if (← ReduceM.isNormalizingDef refId) then
      return .done nid
    else
      ReduceM.modifyStats (·.incInstantiation)
      let rootCopy ← copySubgraph def_.root
      let refConsumer ← ReduceM.getConnection (PortId.principal nid)
      ReduceM.disconnect (PortId.principal nid)
      match refConsumer with
      | some consumer => ReduceM.connect consumer rootCopy
      | none => pure ()
      ReduceM.removeNode nid
      ReduceM.trackPeakNodes
      -- Prevent runaway transitive instantiation
      ReduceM.addNormalizingDef refId
      return .demand demandPort

  -- DUP at principal is not reached in demand-driven evaluation
  -- INDEX isn't interpreted here
  | .dup _ | .index =>
    return .done nid

/-- Classify a node reached at an auxiliary port during WHNF -/
partial def stepAtAuxiliary (nid : NodeId) (entry : NodeEntry)
    (_port : PortIdx) (demandPort : PortId) : ReduceM StepResult := do
  match entry.node with
  | .dup label =>
    if ← ReduceM.isResolvingDup nid then
      return .done nid
    let preserveSharing := (← ReduceM.getConfig).preserveSharing
    match ← ReduceM.getConnection (PortId.principal nid) with
    | none => return .done nid
    | some partner =>
      if !partner.port.isPrincipal then
        let partnerEntry ← ReduceM.getNode partner.node
        match partnerEntry.node with
        | .dup _ =>
          if preserveSharing then
            return .done nid
        | _ => return .done nid
    ReduceM.addResolvingDup nid
    return .demandFrame
      (WhnfFrame.dupValue nid label entry.ty demandPort)
      (PortId.principal nid)
  | _ =>
    return .done nid

partial def applyAppFun (appId : NodeId) (demandPort : PortId)
    (value : NodeId) (valEntry : NodeEntry) : ReduceM StepResult := do
    match valEntry.node with
    | .lam erased =>
      let argPort ← ReduceM.getConnection ⟨appId, ⟨2⟩⟩
      let argEntry ← match argPort with
        | some p => ReduceM.getNode p.node
        | none => ReduceM.getNode appId
      let config ← ReduceM.getConfig
      let isWorldArg := match argEntry.ty with
        | .vDataType uid _ => config.worldUid?.any (· == uid)
        | _ => false
      if isWorldArg then
        return .done appId
      ReduceM.modifyStats (·.incBeta)
      if !erased then
        ReduceM.link ⟨appId, ⟨2⟩⟩ ⟨value, ⟨1⟩⟩
      else
        erasePort ⟨appId, ⟨2⟩⟩
        ReduceM.disconnect ⟨value, ⟨1⟩⟩
      ReduceM.link ⟨appId, .principal⟩ ⟨value, ⟨2⟩⟩
      ReduceM.disconnect ⟨appId, ⟨1⟩⟩
      ReduceM.removeNode appId
      ReduceM.removeNode value
      ReduceM.trackPeakNodes
      return .demand demandPort
    | .sup supLabel =>
      if (← ReduceM.getConfig).preserveSharing then
        return .done appId
      let appEntry ← ReduceM.getNode appId
      ReduceM.modifyStats (·.incSupCommutation)
      let argTy ← match appEntry.getPort ⟨2⟩ with
        | some p => pure (← ReduceM.getNode p.node).ty
        | none => pure appEntry.ty
      let dupArg ← ReduceM.addNode (.dup supLabel) argTy
      ReduceM.rewirePort ⟨appId, ⟨2⟩⟩ (PortId.principal dupArg)
      let app0 ← ReduceM.addNode .app appEntry.ty
      let app1 ← ReduceM.addNode .app appEntry.ty
      ReduceM.rewirePort ⟨value, ⟨1⟩⟩ ⟨app0, ⟨1⟩⟩
      ReduceM.rewirePort ⟨value, ⟨2⟩⟩ ⟨app1, ⟨1⟩⟩
      ReduceM.connect ⟨dupArg, ⟨1⟩⟩ ⟨app0, ⟨2⟩⟩
      ReduceM.connect ⟨dupArg, ⟨2⟩⟩ ⟨app1, ⟨2⟩⟩
      let resSup ← ReduceM.addNode (.sup supLabel) appEntry.ty
      ReduceM.connect (PortId.principal app0) ⟨resSup, ⟨1⟩⟩
      ReduceM.connect (PortId.principal app1) ⟨resSup, ⟨2⟩⟩
      ReduceM.rewirePort ⟨appId, .principal⟩ (PortId.principal resSup)
      ReduceM.disconnect ⟨appId, ⟨1⟩⟩
      ReduceM.removeNode appId
      ReduceM.removeNode value
      ReduceM.trackPeakNodes
      return .demand demandPort
    | .era =>
      ReduceM.modifyStats (·.incEraAbsorption)
      erasePort ⟨appId, ⟨2⟩⟩
      let eraResult ← ReduceM.addNode .era
      ReduceM.rewirePort ⟨appId, .principal⟩ (PortId.principal eraResult)
      ReduceM.disconnect ⟨appId, ⟨1⟩⟩
      ReduceM.removeNode appId
      ReduceM.removeNode value
      return .demand demandPort
    | .ctor tag 2 =>
      if tag == 0xFFFE then
        let envIsEra ← do
          match valEntry.getPort ⟨2⟩ with
          | some envPort =>
            let envEntry ← ReduceM.getNode envPort.node
            pure (match envEntry.node with | .era => true | _ => false)
          | none => pure true
        let appEntry ← ReduceM.getNode appId
        if envIsEra then
          ReduceM.link ⟨appId, ⟨1⟩⟩ ⟨value, ⟨1⟩⟩
          ReduceM.disconnect ⟨value, ⟨2⟩⟩
          ReduceM.removeNode value
          ReduceM.trackPeakNodes
          return .demand demandPort
        else
          let innerApp ← ReduceM.addNode .app appEntry.ty
          ReduceM.rewirePort ⟨value, ⟨1⟩⟩ ⟨innerApp, ⟨1⟩⟩
          ReduceM.rewirePort ⟨value, ⟨2⟩⟩ ⟨innerApp, ⟨2⟩⟩
          ReduceM.disconnect ⟨appId, ⟨1⟩⟩
          ReduceM.connect ⟨appId, ⟨1⟩⟩ (PortId.principal innerApp)
          ReduceM.removeNode value
          ReduceM.trackPeakNodes
          return .demand demandPort
      else
        return .done appId
    | _ =>
      return .done appId

partial def applyOp2Left (op2Id : NodeId) (op : Op2Code) (demandPort : PortId)
    (value : NodeId) (valEntry : NodeEntry) : ReduceM StepResult := do
    match valEntry.node with
    | .era =>
      ReduceM.modifyStats (·.incEraAbsorption)
      erasePort ⟨op2Id, ⟨2⟩⟩
      let eraResult ← ReduceM.addNode .era
      ReduceM.rewirePort ⟨op2Id, .principal⟩ (PortId.principal eraResult)
      ReduceM.disconnect ⟨op2Id, ⟨1⟩⟩
      ReduceM.removeNode op2Id
      ReduceM.removeNode value
      return .demand demandPort
    | .sup supLabel =>
      if (← ReduceM.getConfig).preserveSharing then
        return .done op2Id
      let op2Entry ← ReduceM.getNode op2Id
      ReduceM.modifyStats (·.incSupCommutation)
      let dupRight ← ReduceM.addNode (.dup supLabel) op2Entry.ty
      ReduceM.rewirePort ⟨op2Id, ⟨2⟩⟩ (PortId.principal dupRight)
      let op0 ← ReduceM.addNode (.op2 op) op2Entry.ty
      let op1 ← ReduceM.addNode (.op2 op) op2Entry.ty
      ReduceM.rewirePort ⟨value, ⟨1⟩⟩ ⟨op0, ⟨1⟩⟩
      ReduceM.rewirePort ⟨value, ⟨2⟩⟩ ⟨op1, ⟨1⟩⟩
      ReduceM.connect ⟨dupRight, ⟨1⟩⟩ ⟨op0, ⟨2⟩⟩
      ReduceM.connect ⟨dupRight, ⟨2⟩⟩ ⟨op1, ⟨2⟩⟩
      let resSup ← ReduceM.addNode (.sup supLabel) op2Entry.ty
      ReduceM.connect (PortId.principal op0) ⟨resSup, ⟨1⟩⟩
      ReduceM.connect (PortId.principal op1) ⟨resSup, ⟨2⟩⟩
      ReduceM.rewirePort ⟨op2Id, .principal⟩ (PortId.principal resSup)
      ReduceM.disconnect ⟨op2Id, ⟨1⟩⟩
      ReduceM.removeNode op2Id
      ReduceM.removeNode value
      ReduceM.trackPeakNodes
      return .demand demandPort
    | .num ptL vL =>
      let op2Entry ← ReduceM.getNode op2Id
      return .demandFrame
        (WhnfFrame.op2Right op2Id op op2Entry.ty value ptL vL valEntry.ty demandPort)
        ⟨op2Id, ⟨2⟩⟩
    | _ =>
      let rightId ← whnf ⟨op2Id, ⟨2⟩⟩
      let rightEntry ← ReduceM.getNode rightId
      match rightEntry.node with
      | .num ptR vR =>
        match algebraicSimplify? op vR false with
        | some .identity =>
          ReduceM.modifyStats (·.incArithmetic)
          ReduceM.link ⟨op2Id, .principal⟩ ⟨op2Id, ⟨1⟩⟩
          ReduceM.disconnect ⟨op2Id, ⟨2⟩⟩
          ReduceM.removeNode op2Id
          ReduceM.removeNode rightId
          return .demand demandPort
        | some (.absorb absorbVal) =>
          ReduceM.modifyStats (·.incArithmetic)
          erasePort ⟨op2Id, ⟨1⟩⟩
          let resultNode ← ReduceM.addNode (.num ptR absorbVal) rightEntry.ty
          ReduceM.rewirePort ⟨op2Id, .principal⟩ (PortId.principal resultNode)
          ReduceM.disconnect ⟨op2Id, ⟨2⟩⟩
          ReduceM.removeNode op2Id
          ReduceM.removeNode rightId
          return .demand demandPort
        | none => return .done op2Id
      | _ => return .done op2Id

partial def applyOp2Right (op2Id : NodeId) (op : Op2Code) (leftId : NodeId)
    (ptL : PrimType) (vL : UInt32) (leftTy : Value) (demandPort : PortId)
    (value : NodeId) (valEntry : NodeEntry) : ReduceM StepResult := do
    match valEntry.node with
    | .era =>
      ReduceM.modifyStats (·.incEraAbsorption)
      let eraResult ← ReduceM.addNode .era
      ReduceM.rewirePort ⟨op2Id, .principal⟩ (PortId.principal eraResult)
      ReduceM.disconnect ⟨op2Id, ⟨1⟩⟩
      ReduceM.disconnect ⟨op2Id, ⟨2⟩⟩
      ReduceM.removeNode op2Id
      ReduceM.removeNode leftId
      ReduceM.removeNode value
      return .demand demandPort
    | .sup supLabel =>
      if (← ReduceM.getConfig).preserveSharing then
        return .done op2Id
      let op2Entry ← ReduceM.getNode op2Id
      ReduceM.modifyStats (·.incSupCommutation)
      let numCopy0 ← ReduceM.addNode (.num ptL vL) leftTy
      let numCopy1 ← ReduceM.addNode (.num ptL vL) leftTy
      let op0 ← ReduceM.addNode (.op2 op) op2Entry.ty
      let op1 ← ReduceM.addNode (.op2 op) op2Entry.ty
      ReduceM.connect (PortId.principal numCopy0) ⟨op0, ⟨1⟩⟩
      ReduceM.connect (PortId.principal numCopy1) ⟨op1, ⟨1⟩⟩
      ReduceM.rewirePort ⟨value, ⟨1⟩⟩ ⟨op0, ⟨2⟩⟩
      ReduceM.rewirePort ⟨value, ⟨2⟩⟩ ⟨op1, ⟨2⟩⟩
      let resSup ← ReduceM.addNode (.sup supLabel) op2Entry.ty
      ReduceM.connect (PortId.principal op0) ⟨resSup, ⟨1⟩⟩
      ReduceM.connect (PortId.principal op1) ⟨resSup, ⟨2⟩⟩
      ReduceM.rewirePort ⟨op2Id, .principal⟩ (PortId.principal resSup)
      ReduceM.disconnect ⟨op2Id, ⟨1⟩⟩
      ReduceM.disconnect ⟨op2Id, ⟨2⟩⟩
      ReduceM.removeNode op2Id
      ReduceM.removeNode leftId
      ReduceM.removeNode value
      ReduceM.trackPeakNodes
      return .demand demandPort
    | .num _ vR =>
      ReduceM.modifyStats (·.incArithmetic)
      match computeOp2 op vL vR with
      | .ok result =>
        let config ← ReduceM.getConfig
        let boolValueTy : Value :=
          match config.boolUid? with
          | some uid => .vDataType uid []
          | none     => .vType Soma.Core.Level.zero
        let (resPt, resTy) := match op with
          | .eq | .ne | .lt | .le | .gt | .ge => (PrimType.bool, boolValueTy)
          | _ => (ptL, leftTy)
        let resultNode ← ReduceM.addNode (.num resPt result) resTy
        ReduceM.rewirePort ⟨op2Id, .principal⟩ (PortId.principal resultNode)
        ReduceM.disconnect ⟨op2Id, ⟨1⟩⟩
        ReduceM.disconnect ⟨op2Id, ⟨2⟩⟩
        ReduceM.removeNode op2Id
        ReduceM.removeNode leftId
        ReduceM.removeNode value
        return .demand demandPort
      | .error e => throw e
    | _ =>
      match algebraicSimplify? op vL true with
      | some .identity =>
        ReduceM.modifyStats (·.incArithmetic)
        ReduceM.link ⟨op2Id, .principal⟩ ⟨op2Id, ⟨2⟩⟩
        ReduceM.disconnect ⟨op2Id, ⟨1⟩⟩
        ReduceM.removeNode op2Id
        ReduceM.removeNode leftId
        return .demand demandPort
      | some (.absorb absorbVal) =>
        ReduceM.modifyStats (·.incArithmetic)
        erasePort ⟨op2Id, ⟨2⟩⟩
        let resultNode ← ReduceM.addNode (.num ptL absorbVal) leftTy
        ReduceM.rewirePort ⟨op2Id, .principal⟩ (PortId.principal resultNode)
        ReduceM.disconnect ⟨op2Id, ⟨1⟩⟩
        ReduceM.removeNode op2Id
        ReduceM.removeNode leftId
        return .demand demandPort
      | none => return .done op2Id

partial def applyOp1Operand (op1Id : NodeId) (op : Op1Code) (demandPort : PortId)
    (value : NodeId) (valEntry : NodeEntry) : ReduceM StepResult := do
    match valEntry.node with
    | .era =>
      ReduceM.modifyStats (·.incEraAbsorption)
      let eraResult ← ReduceM.addNode .era
      ReduceM.rewirePort ⟨op1Id, .principal⟩ (PortId.principal eraResult)
      ReduceM.disconnect ⟨op1Id, ⟨1⟩⟩
      ReduceM.removeNode op1Id
      ReduceM.removeNode value
      return .demand demandPort
    | .sup supLabel =>
      if (← ReduceM.getConfig).preserveSharing then
        return .done op1Id
      let op1Entry ← ReduceM.getNode op1Id
      ReduceM.modifyStats (·.incSupCommutation)
      let op0 ← ReduceM.addNode (.op1 op) op1Entry.ty
      let op1 ← ReduceM.addNode (.op1 op) op1Entry.ty
      ReduceM.rewirePort ⟨value, ⟨1⟩⟩ ⟨op0, ⟨1⟩⟩
      ReduceM.rewirePort ⟨value, ⟨2⟩⟩ ⟨op1, ⟨1⟩⟩
      let resSup ← ReduceM.addNode (.sup supLabel) op1Entry.ty
      ReduceM.connect (PortId.principal op0) ⟨resSup, ⟨1⟩⟩
      ReduceM.connect (PortId.principal op1) ⟨resSup, ⟨2⟩⟩
      ReduceM.rewirePort ⟨op1Id, .principal⟩ (PortId.principal resSup)
      ReduceM.disconnect ⟨op1Id, ⟨1⟩⟩
      ReduceM.removeNode op1Id
      ReduceM.removeNode value
      ReduceM.trackPeakNodes
      return .demand demandPort
    | .num pt v =>
      ReduceM.modifyStats (·.incArithmetic)
      let result := computeOp1 op v
      let resPt := match op with
        | .not => PrimType.bool
        | .neg => pt
      let resultNode ← ReduceM.addNode (.num resPt result) valEntry.ty
      ReduceM.rewirePort ⟨op1Id, .principal⟩ (PortId.principal resultNode)
      ReduceM.disconnect ⟨op1Id, ⟨1⟩⟩
      ReduceM.removeNode op1Id
      ReduceM.removeNode value
      return .demand demandPort
    | _ =>
      return .done op1Id

partial def applyMatScrutinee (matId : NodeId) (expectedTag : Nat) (demandPort : PortId)
    (value : NodeId) (valEntry : NodeEntry) : ReduceM StepResult := do
    match valEntry.node with
    | .era =>
      ReduceM.modifyStats (·.incEraAbsorption)
      erasePort ⟨matId, ⟨2⟩⟩
      erasePort ⟨matId, ⟨3⟩⟩
      let eraResult ← ReduceM.addNode .era
      ReduceM.rewirePort ⟨matId, .principal⟩ (PortId.principal eraResult)
      ReduceM.disconnect ⟨matId, ⟨1⟩⟩
      ReduceM.removeNode matId
      ReduceM.removeNode value
      return .demand demandPort
    | .sup supLabel =>
      if (← ReduceM.getConfig).preserveSharing then
        return .done matId
      let matEntry ← ReduceM.getNode matId
      ReduceM.modifyStats (·.incSupCommutation)
      let hitTy ← match matEntry.getPort ⟨2⟩ with
        | some p => pure (← ReduceM.getNode p.node).ty
        | none => pure matEntry.ty
      let missTy ← match matEntry.getPort ⟨3⟩ with
        | some p => pure (← ReduceM.getNode p.node).ty
        | none => pure matEntry.ty
      let dupHit ← ReduceM.addNode (.dup supLabel) hitTy
      let dupMiss ← ReduceM.addNode (.dup supLabel) missTy
      ReduceM.rewirePort ⟨matId, ⟨2⟩⟩ (PortId.principal dupHit)
      ReduceM.rewirePort ⟨matId, ⟨3⟩⟩ (PortId.principal dupMiss)
      let mat0 ← ReduceM.addNode (.mat expectedTag) matEntry.ty
      let mat1 ← ReduceM.addNode (.mat expectedTag) matEntry.ty
      ReduceM.rewirePort ⟨value, ⟨1⟩⟩ ⟨mat0, ⟨1⟩⟩
      ReduceM.rewirePort ⟨value, ⟨2⟩⟩ ⟨mat1, ⟨1⟩⟩
      ReduceM.connect ⟨dupHit, ⟨1⟩⟩ ⟨mat0, ⟨2⟩⟩
      ReduceM.connect ⟨dupHit, ⟨2⟩⟩ ⟨mat1, ⟨2⟩⟩
      ReduceM.connect ⟨dupMiss, ⟨1⟩⟩ ⟨mat0, ⟨3⟩⟩
      ReduceM.connect ⟨dupMiss, ⟨2⟩⟩ ⟨mat1, ⟨3⟩⟩
      let resSup ← ReduceM.addNode (.sup supLabel) matEntry.ty
      ReduceM.connect (PortId.principal mat0) ⟨resSup, ⟨1⟩⟩
      ReduceM.connect (PortId.principal mat1) ⟨resSup, ⟨2⟩⟩
      ReduceM.rewirePort ⟨matId, .principal⟩ (PortId.principal resSup)
      ReduceM.disconnect ⟨matId, ⟨1⟩⟩
      ReduceM.removeNode matId
      ReduceM.removeNode value
      ReduceM.trackPeakNodes
      return .demand demandPort
    | .ctor tag _arity =>
      ReduceM.modifyStats (·.incMatch)
      if tag == expectedTag then
        ReduceM.link ⟨matId, .principal⟩ ⟨matId, ⟨2⟩⟩
        erasePort ⟨matId, ⟨3⟩⟩
      else
        ReduceM.link ⟨matId, .principal⟩ ⟨matId, ⟨3⟩⟩
        erasePort ⟨matId, ⟨2⟩⟩
      erasePort ⟨matId, ⟨1⟩⟩
      ReduceM.removeNode matId
      return .demand demandPort
    | .num _ v =>
      ReduceM.modifyStats (·.incMatch)
      if v.toNat == expectedTag then
        ReduceM.link ⟨matId, .principal⟩ ⟨matId, ⟨2⟩⟩
        erasePort ⟨matId, ⟨3⟩⟩
      else
        ReduceM.link ⟨matId, .principal⟩ ⟨matId, ⟨3⟩⟩
        erasePort ⟨matId, ⟨2⟩⟩
      erasePort ⟨matId, ⟨1⟩⟩
      ReduceM.removeNode matId
      return .demand demandPort
    | .array _ =>
      let lenId ← whnf ⟨value, ⟨1⟩⟩
      let lenEntry ← ReduceM.getNode lenId
      match lenEntry.node with
      | .num _ v =>
        let isHit := if expectedTag == 0 then v.toNat == 0
                     else if expectedTag == 1 then v.toNat > 0
                     else false
        ReduceM.modifyStats (·.incMatch)
        if isHit then
          ReduceM.link ⟨matId, .principal⟩ ⟨matId, ⟨2⟩⟩
          erasePort ⟨matId, ⟨3⟩⟩
        else
          ReduceM.link ⟨matId, .principal⟩ ⟨matId, ⟨3⟩⟩
          erasePort ⟨matId, ⟨2⟩⟩
        erasePort ⟨matId, ⟨1⟩⟩
        ReduceM.removeNode matId
        return .demand demandPort
      | _ => return .done matId
    | _ => return .done matId

partial def applyProjRecord (projId : NodeId) (fieldIdx : Nat) (demandPort : PortId)
    (value : NodeId) (valEntry : NodeEntry) : ReduceM StepResult := do
    match valEntry.node with
    | .era =>
      ReduceM.modifyStats (·.incEraAbsorption)
      let eraResult ← ReduceM.addNode .era
      ReduceM.rewirePort ⟨projId, .principal⟩ (PortId.principal eraResult)
      ReduceM.disconnect ⟨projId, ⟨1⟩⟩
      ReduceM.removeNode projId
      ReduceM.removeNode value
      return .demand demandPort
    | .sup supLabel =>
      if (← ReduceM.getConfig).preserveSharing then
        return .done projId
      let projEntry ← ReduceM.getNode projId
      ReduceM.modifyStats (·.incSupCommutation)
      let proj0 ← ReduceM.addNode (.proj fieldIdx) projEntry.ty
      let proj1 ← ReduceM.addNode (.proj fieldIdx) projEntry.ty
      ReduceM.rewirePort ⟨value, ⟨1⟩⟩ ⟨proj0, ⟨1⟩⟩
      ReduceM.rewirePort ⟨value, ⟨2⟩⟩ ⟨proj1, ⟨1⟩⟩
      let resSup ← ReduceM.addNode (.sup supLabel) projEntry.ty
      ReduceM.connect (PortId.principal proj0) ⟨resSup, ⟨1⟩⟩
      ReduceM.connect (PortId.principal proj1) ⟨resSup, ⟨2⟩⟩
      ReduceM.rewirePort ⟨projId, .principal⟩ (PortId.principal resSup)
      ReduceM.disconnect ⟨projId, ⟨1⟩⟩
      ReduceM.removeNode projId
      ReduceM.removeNode value
      ReduceM.trackPeakNodes
      return .demand demandPort
    | .record numFields =>
      ReduceM.modifyStats (·.incProjection)
      ReduceM.link ⟨projId, .principal⟩ ⟨value, ⟨fieldIdx + 1⟩⟩
      for i in [:numFields] do
        if i != fieldIdx then
          erasePort ⟨value, ⟨i + 1⟩⟩
      ReduceM.disconnect ⟨projId, ⟨1⟩⟩
      ReduceM.removeNode projId
      ReduceM.removeNode value
      return .demand demandPort
    | .ctor _tag arity =>
      ReduceM.modifyStats (·.incProjection)
      ReduceM.link ⟨projId, .principal⟩ ⟨value, ⟨fieldIdx + 1⟩⟩
      for i in [:arity] do
        if i != fieldIdx then
          erasePort ⟨value, ⟨i + 1⟩⟩
      ReduceM.disconnect ⟨projId, ⟨1⟩⟩
      ReduceM.removeNode projId
      ReduceM.removeNode value
      return .demand demandPort
    | .array elemType =>
      ReduceM.modifyStats (·.incProjection)
      if fieldIdx == 0 then
        let dataId ← whnf ⟨value, ⟨2⟩⟩
        let dataEntry ← ReduceM.getNode dataId
        match dataEntry.node with
        | .ctor _ arity =>
          ReduceM.link ⟨projId, .principal⟩ ⟨dataId, ⟨1⟩⟩
          for i in [1:arity] do
            erasePort ⟨dataId, ⟨i + 1⟩⟩
          erasePort ⟨value, ⟨1⟩⟩
          ReduceM.disconnect ⟨value, ⟨2⟩⟩
          ReduceM.disconnect ⟨projId, ⟨1⟩⟩
          ReduceM.removeNode projId
          ReduceM.removeNode dataId
          ReduceM.removeNode value
          return .demand demandPort
        | _ => return .done projId
      else if fieldIdx == 1 then
        let valTyCur := valEntry.ty
        let lenId ← whnf ⟨value, ⟨1⟩⟩
        let lenEntry ← ReduceM.getNode lenId
        let dataId ← whnf ⟨value, ⟨2⟩⟩
        let dataEntry ← ReduceM.getNode dataId
        match lenEntry.node, dataEntry.node with
        | .num pt v, .ctor _ arity =>
          let newLen := v - 1
          let newArity := arity - 1
          let newLenNode ← ReduceM.addNode (.num pt newLen) lenEntry.ty
          let newDataNode ← ReduceM.addNode (.ctor 0xFFFD newArity) valTyCur
          for i in [:newArity] do
            ReduceM.rewirePort ⟨dataId, ⟨i + 2⟩⟩ ⟨newDataNode, ⟨i + 1⟩⟩
          erasePort ⟨dataId, ⟨1⟩⟩
          let newArrayNode ← ReduceM.addNode (.array elemType) valTyCur
          ReduceM.connect ⟨newArrayNode, ⟨1⟩⟩ (PortId.principal newLenNode)
          ReduceM.connect ⟨newArrayNode, ⟨2⟩⟩ (PortId.principal newDataNode)
          ReduceM.rewirePort ⟨projId, .principal⟩ (PortId.principal newArrayNode)
          ReduceM.disconnect ⟨value, ⟨1⟩⟩
          ReduceM.disconnect ⟨value, ⟨2⟩⟩
          ReduceM.disconnect ⟨projId, ⟨1⟩⟩
          ReduceM.removeNode projId
          ReduceM.removeNode dataId
          ReduceM.removeNode lenId
          ReduceM.removeNode value
          ReduceM.trackPeakNodes
          return .demand demandPort
        | _, _ => return .done projId
      else return .done projId
    | _ => return .done projId

partial def applyDupValue (dupId : NodeId) (label : Label) (demandPort : PortId)
    (value : NodeId) (valEntry : NodeEntry) : ReduceM StepResult := do
    ReduceM.removeResolvingDup dupId
    let preserveSharing := (← ReduceM.getConfig).preserveSharing
    match ← ReduceM.getConnection (PortId.principal dupId) with
    | none => return .done dupId
    | some partner =>
      unless partner.port.isPrincipal do
        return .done dupId
    match valEntry.node with
    | .num pt v =>
      ReduceM.modifyStats (·.incDupCommutation)
      let copy0 ← ReduceM.addNode (.num pt v) valEntry.ty
      let copy1 ← ReduceM.addNode (.num pt v) valEntry.ty
      ReduceM.rewirePort ⟨dupId, ⟨1⟩⟩ (PortId.principal copy0)
      ReduceM.rewirePort ⟨dupId, ⟨2⟩⟩ (PortId.principal copy1)
      ReduceM.disconnect (PortId.principal dupId)
      ReduceM.removeNode dupId
      ReduceM.removeNode value
      ReduceM.trackPeakNodes
      return .demand demandPort
    | .num64 pt lo hi =>
      ReduceM.modifyStats (·.incDupCommutation)
      let copy0 ← ReduceM.addNode (.num64 pt lo hi) valEntry.ty
      let copy1 ← ReduceM.addNode (.num64 pt lo hi) valEntry.ty
      ReduceM.rewirePort ⟨dupId, ⟨1⟩⟩ (PortId.principal copy0)
      ReduceM.rewirePort ⟨dupId, ⟨2⟩⟩ (PortId.principal copy1)
      ReduceM.disconnect (PortId.principal dupId)
      ReduceM.removeNode dupId
      ReduceM.removeNode value
      ReduceM.trackPeakNodes
      return .demand demandPort
    | .era =>
      ReduceM.modifyStats (·.incDupEraAnnihilation)
      let era0 ← ReduceM.addNode .era
      let era1 ← ReduceM.addNode .era
      ReduceM.rewirePort ⟨dupId, ⟨1⟩⟩ (PortId.principal era0)
      ReduceM.rewirePort ⟨dupId, ⟨2⟩⟩ (PortId.principal era1)
      ReduceM.disconnect (PortId.principal dupId)
      ReduceM.removeNode dupId
      ReduceM.removeNode value
      return .demand demandPort
    | .lam erased =>
      if preserveSharing then
        return .done dupId
      ReduceM.modifyStats (·.incDupCommutation)
      let lam0 ← ReduceM.addNode (.lam erased) valEntry.ty
      let lam1 ← ReduceM.addNode (.lam erased) valEntry.ty
      let varTy := valEntry.ty.piDomain?.getD valEntry.ty
      let bodyTy := match valEntry.ty with
        | .vPi _ _ name dom cod =>
          match cod with
          | .const _ v' => v'
          | .term _ env _ =>
            let dummyArg := Value.vNeutral dom (.nVar ⟨name, env.level⟩)
            cod.applyPure dummyArg
        | _ => valEntry.ty
      if !erased then
        let dupVar ← ReduceM.addNode (.dup label) varTy
        ReduceM.rewirePort ⟨value, ⟨1⟩⟩ (PortId.principal dupVar)
        ReduceM.connect ⟨dupVar, ⟨1⟩⟩ ⟨lam0, ⟨1⟩⟩
        ReduceM.connect ⟨dupVar, ⟨2⟩⟩ ⟨lam1, ⟨1⟩⟩
      else
        let eraVar0 ← ReduceM.addNode .era
        let eraVar1 ← ReduceM.addNode .era
        ReduceM.connect (PortId.principal eraVar0) ⟨lam0, ⟨1⟩⟩
        ReduceM.connect (PortId.principal eraVar1) ⟨lam1, ⟨1⟩⟩
        ReduceM.disconnect ⟨value, ⟨1⟩⟩
      let dupBody ← ReduceM.addNode (.dup label) bodyTy
      ReduceM.rewirePort ⟨value, ⟨2⟩⟩ (PortId.principal dupBody)
      ReduceM.connect ⟨dupBody, ⟨1⟩⟩ ⟨lam0, ⟨2⟩⟩
      ReduceM.connect ⟨dupBody, ⟨2⟩⟩ ⟨lam1, ⟨2⟩⟩
      ReduceM.rewirePort ⟨dupId, ⟨1⟩⟩ (PortId.principal lam0)
      ReduceM.rewirePort ⟨dupId, ⟨2⟩⟩ (PortId.principal lam1)
      ReduceM.disconnect (PortId.principal dupId)
      ReduceM.removeNode dupId
      ReduceM.removeNode value
      ReduceM.trackPeakNodes
      return .demand demandPort
    | .sup supLabel =>
      if label == supLabel then
        ReduceM.modifyStats (·.incDupSupAnnihilation)
        ReduceM.link ⟨dupId, ⟨1⟩⟩ ⟨value, ⟨1⟩⟩
        ReduceM.link ⟨dupId, ⟨2⟩⟩ ⟨value, ⟨2⟩⟩
        ReduceM.disconnect (PortId.principal dupId)
        ReduceM.removeNode dupId
        ReduceM.removeNode value
        return .demand demandPort
      else if preserveSharing then
        return .done dupId
      else
        ReduceM.modifyStats (·.incDupSupCommutation)
        let tyA ← match valEntry.getPort ⟨1⟩ with
          | some p => pure (← ReduceM.getNode p.node).ty
          | none => pure valEntry.ty
        let tyB ← match valEntry.getPort ⟨2⟩ with
          | some p => pure (← ReduceM.getNode p.node).ty
          | none => pure valEntry.ty
        let dupA ← ReduceM.addNode (.dup label) tyA
        let dupB ← ReduceM.addNode (.dup label) tyB
        let sup0 ← ReduceM.addNode (.sup supLabel) valEntry.ty
        let sup1 ← ReduceM.addNode (.sup supLabel) valEntry.ty
        ReduceM.rewirePort ⟨value, ⟨1⟩⟩ (PortId.principal dupA)
        ReduceM.rewirePort ⟨value, ⟨2⟩⟩ (PortId.principal dupB)
        ReduceM.connect ⟨dupA, ⟨1⟩⟩ ⟨sup0, ⟨1⟩⟩
        ReduceM.connect ⟨dupA, ⟨2⟩⟩ ⟨sup1, ⟨1⟩⟩
        ReduceM.connect ⟨dupB, ⟨1⟩⟩ ⟨sup0, ⟨2⟩⟩
        ReduceM.connect ⟨dupB, ⟨2⟩⟩ ⟨sup1, ⟨2⟩⟩
        ReduceM.rewirePort ⟨dupId, ⟨1⟩⟩ (PortId.principal sup0)
        ReduceM.rewirePort ⟨dupId, ⟨2⟩⟩ (PortId.principal sup1)
        ReduceM.disconnect (PortId.principal dupId)
        ReduceM.removeNode dupId
        ReduceM.removeNode value
        ReduceM.trackPeakNodes
        return .demand demandPort
    | .dup innerLabel =>
      if label == innerLabel then
        ReduceM.modifyStats (·.incDupSupAnnihilation)
        ReduceM.link ⟨dupId, ⟨1⟩⟩ ⟨value, ⟨1⟩⟩
        ReduceM.link ⟨dupId, ⟨2⟩⟩ ⟨value, ⟨2⟩⟩
        ReduceM.disconnect (PortId.principal dupId)
        ReduceM.removeNode dupId
        ReduceM.removeNode value
        return .demand demandPort
      else if preserveSharing then
        return .done dupId
      else
        ReduceM.modifyStats (·.incDupSupCommutation)
        let tyA ← match valEntry.getPort ⟨1⟩ with
          | some p => pure (← ReduceM.getNode p.node).ty
          | none => pure valEntry.ty
        let tyB ← match valEntry.getPort ⟨2⟩ with
          | some p => pure (← ReduceM.getNode p.node).ty
          | none => pure valEntry.ty
        let dupA ← ReduceM.addNode (.dup label) tyA
        let dupB ← ReduceM.addNode (.dup label) tyB
        let dup0 ← ReduceM.addNode (.dup innerLabel) tyA
        let dup1 ← ReduceM.addNode (.dup innerLabel) tyB
        ReduceM.rewirePort ⟨value, ⟨1⟩⟩ (PortId.principal dupA)
        ReduceM.rewirePort ⟨value, ⟨2⟩⟩ (PortId.principal dupB)
        ReduceM.connect ⟨dupA, ⟨1⟩⟩ ⟨dup0, ⟨1⟩⟩
        ReduceM.connect ⟨dupA, ⟨2⟩⟩ ⟨dup1, ⟨1⟩⟩
        ReduceM.connect ⟨dupB, ⟨1⟩⟩ ⟨dup0, ⟨2⟩⟩
        ReduceM.connect ⟨dupB, ⟨2⟩⟩ ⟨dup1, ⟨2⟩⟩
        ReduceM.rewirePort ⟨dupId, ⟨1⟩⟩ (PortId.principal dup0)
        ReduceM.rewirePort ⟨dupId, ⟨2⟩⟩ (PortId.principal dup1)
        ReduceM.disconnect (PortId.principal dupId)
        ReduceM.removeNode dupId
        ReduceM.removeNode value
        ReduceM.trackPeakNodes
        return .demand demandPort
    | other =>
      let arity := other.numAuxPorts
      if arity == 0 then
        ReduceM.modifyStats (·.incDupCommutation)
        let copy0 ← ReduceM.addNode other valEntry.ty
        let copy1 ← ReduceM.addNode other valEntry.ty
        ReduceM.rewirePort ⟨dupId, ⟨1⟩⟩ (PortId.principal copy0)
        ReduceM.rewirePort ⟨dupId, ⟨2⟩⟩ (PortId.principal copy1)
        ReduceM.disconnect (PortId.principal dupId)
        ReduceM.removeNode dupId
        ReduceM.removeNode value
        ReduceM.trackPeakNodes
        return .demand demandPort
      else if preserveSharing then
        return .done dupId
      else
        ReduceM.modifyStats (·.incDupCommutation)
        let node0 ← ReduceM.addNode other valEntry.ty
        let node1 ← ReduceM.addNode other valEntry.ty
        for i in [:arity] do
          let fieldTy ← do
            match valEntry.getPort ⟨i + 1⟩ with
            | some fieldPort =>
              let fieldEntry ← ReduceM.getNode fieldPort.node
              pure fieldEntry.ty
            | none => pure valEntry.ty
          let dupField ← ReduceM.addNode (.dup label) fieldTy
          ReduceM.rewirePort ⟨value, ⟨i + 1⟩⟩ (PortId.principal dupField)
          ReduceM.connect ⟨dupField, ⟨1⟩⟩ ⟨node0, ⟨i + 1⟩⟩
          ReduceM.connect ⟨dupField, ⟨2⟩⟩ ⟨node1, ⟨i + 1⟩⟩
        ReduceM.rewirePort ⟨dupId, ⟨1⟩⟩ (PortId.principal node0)
        ReduceM.rewirePort ⟨dupId, ⟨2⟩⟩ (PortId.principal node1)
        ReduceM.disconnect (PortId.principal dupId)
        ReduceM.removeNode dupId
        ReduceM.removeNode value
        ReduceM.trackPeakNodes
        return .demand demandPort

partial def applyUseTerm (useId : NodeId) (demandPort : PortId)
    (value : NodeId) : ReduceM StepResult := do
    let useEntry ← ReduceM.getNode useId
    let termConn := useEntry.getPort ⟨1⟩
    let reachesPrincipalValue : Bool ← do
      match termConn with
      | none => pure false
      | some tp =>
        if !tp.port.isPrincipal then
          pure false
        else
          let termNodeEntry ← ReduceM.getNode tp.node
          pure (match termNodeEntry.node with
            | .num _ _ | .num64 _ _ _ | .era | .ctor _ _ | .record _
            | .string | .array _ | .lam _ | .sup _ => true
            | _ => false)
    if reachesPrincipalValue then
      ReduceM.modifyStats (·.incUse)
      erasePort ⟨useId, ⟨1⟩⟩
      ReduceM.link ⟨useId, .principal⟩ ⟨useId, ⟨2⟩⟩
      ReduceM.removeNode useId
      return .demand demandPort
    else
      return .done useId

partial def applyFrame (frame : WhnfFrame) (value : NodeId) : ReduceM StepResult := do
  let valEntry ← ReduceM.getNode value
  match frame with
  | .appFun appId _ demandPort => applyAppFun appId demandPort value valEntry
  | .op2Left op2Id op _ demandPort => applyOp2Left op2Id op demandPort value valEntry
  | .op2Right op2Id op _ leftId ptL vL leftTy demandPort =>
    applyOp2Right op2Id op leftId ptL vL leftTy demandPort value valEntry
  | .op1Operand op1Id op _ demandPort => applyOp1Operand op1Id op demandPort value valEntry
  | .matScrutinee matId expectedTag _ demandPort =>
    applyMatScrutinee matId expectedTag demandPort value valEntry
  | .projRecord projId fieldIdx _ demandPort =>
    applyProjRecord projId fieldIdx demandPort value valEntry
  | .dupValue dupId label _ demandPort => applyDupValue dupId label demandPort value valEntry
  | .useTerm useId demandPort => applyUseTerm useId demandPort value

/-- Tail-recursive trampoline driver for WHNF reduction -/
partial def whnfLoop (stack : List WhnfFrame) (value? : Option NodeId)
    (demand : PortId) : ReduceM NodeId := do
  match value? with
  | some value =>
    match stack with
    | [] => return value
    | frame :: rest =>
      match ← applyFrame frame value with
      | .done nid => whnfLoop rest (some nid) demand
      | .demand p => whnfLoop rest none p
      | .demandFrame f p => whnfLoop (f :: rest) none p
  | none =>
    ReduceM.consumeFuel
    let target ← ReduceM.follow demand
    let entry ← ReduceM.getNode target.node
    let sr ← if target.port.isPrincipal then
      stepAtPrincipal target.node entry demand
    else
      stepAtAuxiliary target.node entry target.port demand
    match sr with
    | .done nid => whnfLoop stack (some nid) demand
    | .demand p => whnfLoop stack none p
    | .demandFrame f p => whnfLoop (f :: stack) none p

/-- Evaluate a port to weak head normal form -/
partial def whnf (initialPort : PortId) : ReduceM NodeId :=
  whnfLoop [] none initialPort

end -- mutual

end Somac.Circuit.Reduce
