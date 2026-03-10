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

mutual

/-- Connect an ERA node to whatever is connected to the given port, consuming that subgraph -/
partial def erasePort (port : PortId) : ReduceM Unit := do
  match ← ReduceM.getConnection port with
  | none => pure ()
  | some target =>
    ReduceM.disconnect port
    -- Create an ERA and connect it to the target
    let era ← ReduceM.addNode .era
    ReduceM.connect (PortId.principal era) target
    -- Eagerly propagate ERA through the target if it's a value node
    propagateEra era target

/-- Eagerly propagate an ERA through the node it's connected to -/
partial def propagateEra (eraId : NodeId) (target : PortId) : ReduceM Unit := do
  let entry ← ReduceM.getNode target.node
  if !target.port.isPrincipal then return
  let arity := entry.node.numAuxPorts
  match entry.node with
  | .lam erased =>
    if arity > 0 then ReduceM.modifyStats (·.incEraPropagation)
    if !erased then
      erasePort ⟨target.node, ⟨1⟩⟩
    else
      ReduceM.disconnect ⟨target.node, ⟨1⟩⟩
    erasePort ⟨target.node, ⟨2⟩⟩
  | _ =>
    if arity > 0 then ReduceM.modifyStats (·.incEraPropagation)
    for i in [:arity] do
      erasePort ⟨target.node, ⟨i + 1⟩⟩
  ReduceM.disconnect (PortId.principal eraId)
  ReduceM.removeNode eraId
  ReduceM.removeNode target.node

end

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

mutual

/-- Resolve a DUP node by evaluating the value it duplicates -/
partial def resolveDup (dupId : NodeId) (label : Label) (demandPort : PortId)
    : ReduceM NodeId := do
  ReduceM.consumeFuel
  -- Evaluate the value connected to DUP's principal port
  let valId ← whnf (PortId.principal dupId)
  let valEntry ← ReduceM.getNode valId
  match valEntry.node with
  | .num pt v =>
    -- DUP-NUM: flat copy (register-width value, zero overhead)
    ReduceM.modifyStats (·.incDupCommutation)
    let copy0 ← ReduceM.addNode (.num pt v) valEntry.ty
    let copy1 ← ReduceM.addNode (.num pt v) valEntry.ty
    -- Wire copies to DUP's consumers (rewirePort: fresh node replaces existing endpoint)
    ReduceM.rewirePort ⟨dupId, ⟨1⟩⟩ (PortId.principal copy0)
    ReduceM.rewirePort ⟨dupId, ⟨2⟩⟩ (PortId.principal copy1)
    -- Clean up
    ReduceM.disconnect (PortId.principal dupId)
    ReduceM.removeNode dupId
    ReduceM.removeNode valId
    ReduceM.trackPeakNodes
    whnf demandPort

  | .era =>
    -- DUP-ERA: value is erased, both consumers get ERA
    ReduceM.modifyStats (·.incDupEraAnnihilation)
    let era0 ← ReduceM.addNode .era
    let era1 ← ReduceM.addNode .era
    ReduceM.rewirePort ⟨dupId, ⟨1⟩⟩ (PortId.principal era0)
    ReduceM.rewirePort ⟨dupId, ⟨2⟩⟩ (PortId.principal era1)
    ReduceM.disconnect (PortId.principal dupId)
    ReduceM.removeNode dupId
    ReduceM.removeNode valId
    whnf demandPort

  | .lam erased =>
    -- DUP-LAM commutation: create two LAMs, DUP their components
    ReduceM.modifyStats (·.incDupCommutation)
    let lam0 ← ReduceM.addNode (.lam erased) valEntry.ty
    let lam1 ← ReduceM.addNode (.lam erased) valEntry.ty

    if !erased then
      -- DUP the variable binding
      let dupVar ← ReduceM.addNode (.dup label) valEntry.ty
      -- DUP_var.principal ← whatever LAM.var was connected to
      ReduceM.rewirePort ⟨valId, ⟨1⟩⟩ (PortId.principal dupVar)
      -- DUP_var.aux0 ← LAM0.var, DUP_var.aux1 ← LAM1.var
      ReduceM.connect ⟨dupVar, ⟨1⟩⟩ ⟨lam0, ⟨1⟩⟩
      ReduceM.connect ⟨dupVar, ⟨2⟩⟩ ⟨lam1, ⟨1⟩⟩
    else
      -- Both vars are erased; connect ERA to each
      let eraVar0 ← ReduceM.addNode .era
      let eraVar1 ← ReduceM.addNode .era
      ReduceM.connect (PortId.principal eraVar0) ⟨lam0, ⟨1⟩⟩
      ReduceM.connect (PortId.principal eraVar1) ⟨lam1, ⟨1⟩⟩
      ReduceM.disconnect ⟨valId, ⟨1⟩⟩

    -- DUP the body
    let dupBody ← ReduceM.addNode (.dup label) valEntry.ty
    ReduceM.rewirePort ⟨valId, ⟨2⟩⟩ (PortId.principal dupBody)
    ReduceM.connect ⟨dupBody, ⟨1⟩⟩ ⟨lam0, ⟨2⟩⟩
    ReduceM.connect ⟨dupBody, ⟨2⟩⟩ ⟨lam1, ⟨2⟩⟩

    -- Wire copies to DUP's consumers
    ReduceM.rewirePort ⟨dupId, ⟨1⟩⟩ (PortId.principal lam0)
    ReduceM.rewirePort ⟨dupId, ⟨2⟩⟩ (PortId.principal lam1)
    -- Clean up original DUP and LAM
    ReduceM.disconnect (PortId.principal dupId)
    ReduceM.removeNode dupId
    ReduceM.removeNode valId
    ReduceM.trackPeakNodes
    whnf demandPort

  | .sup supLabel =>
    if label == supLabel then
      -- DUP-SUP same-label annihilation: O(1), zero copies
      -- DUP^L(SUP^L(a, b)) → (a, b)
      -- Both DUP and SUP ports have existing connections: use link
      ReduceM.modifyStats (·.incDupSupAnnihilation)
      -- SUP.val0 → DUP.copy0's consumer, SUP.val1 → DUP.copy1's consumer
      ReduceM.link ⟨dupId, ⟨1⟩⟩ ⟨valId, ⟨1⟩⟩
      ReduceM.link ⟨dupId, ⟨2⟩⟩ ⟨valId, ⟨2⟩⟩
      ReduceM.disconnect (PortId.principal dupId)
      ReduceM.removeNode dupId
      ReduceM.removeNode valId
      whnf demandPort
    else
      -- DUP-SUP different-label commutation:
      -- DUP^L1(SUP^L2(a, b)) → (SUP^L2(DUP^L1(a)₀, DUP^L1(b)₀),
      --                           SUP^L2(DUP^L1(a)₁, DUP^L1(b)₁))
      ReduceM.modifyStats (·.incDupSupCommutation)
      let dupA ← ReduceM.addNode (.dup label) valEntry.ty
      let dupB ← ReduceM.addNode (.dup label) valEntry.ty
      let sup0 ← ReduceM.addNode (.sup supLabel) valEntry.ty
      let sup1 ← ReduceM.addNode (.sup supLabel) valEntry.ty
      -- Wire DUP_A to value a (SUP.val0): fresh dupA replaces SUP.val0's endpoint
      ReduceM.rewirePort ⟨valId, ⟨1⟩⟩ (PortId.principal dupA)
      -- Wire DUP_B to value b (SUP.val1): fresh dupB replaces SUP.val1's endpoint
      ReduceM.rewirePort ⟨valId, ⟨2⟩⟩ (PortId.principal dupB)
      -- Wire DUP_A outputs to SUP0.val0 and SUP1.val0
      ReduceM.connect ⟨dupA, ⟨1⟩⟩ ⟨sup0, ⟨1⟩⟩
      ReduceM.connect ⟨dupA, ⟨2⟩⟩ ⟨sup1, ⟨1⟩⟩
      -- Wire DUP_B outputs to SUP0.val1 and SUP1.val1
      ReduceM.connect ⟨dupB, ⟨1⟩⟩ ⟨sup0, ⟨2⟩⟩
      ReduceM.connect ⟨dupB, ⟨2⟩⟩ ⟨sup1, ⟨2⟩⟩
      -- Wire new SUPs to DUP's consumers
      ReduceM.rewirePort ⟨dupId, ⟨1⟩⟩ (PortId.principal sup0)
      ReduceM.rewirePort ⟨dupId, ⟨2⟩⟩ (PortId.principal sup1)
      ReduceM.disconnect (PortId.principal dupId)
      ReduceM.removeNode dupId
      ReduceM.removeNode valId
      ReduceM.trackPeakNodes
      whnf demandPort

  | .dup innerLabel =>
    -- DUP-DUP interaction: structurally identical to DUP-SUP.
    -- This arises when DUP-LAM commutation on an identity function (λx.x where
    -- var ↔ body) produces two DUP nodes connected principal-to-principal.
    if label == innerLabel then
      -- DUP-DUP same-label annihilation: O(1), zero copies
      -- DUP^L(DUP^L(a, b)) → (a, b)
      -- Both DUP ports have existing connections: use link
      ReduceM.modifyStats (·.incDupSupAnnihilation)
      ReduceM.link ⟨dupId, ⟨1⟩⟩ ⟨valId, ⟨1⟩⟩
      ReduceM.link ⟨dupId, ⟨2⟩⟩ ⟨valId, ⟨2⟩⟩
      ReduceM.disconnect (PortId.principal dupId)
      ReduceM.removeNode dupId
      ReduceM.removeNode valId
      whnf demandPort
    else
      -- DUP-DUP different-label commutation:
      -- DUP^L1(DUP^L2(a, b)) → (DUP^L2(DUP^L1(a)₀, DUP^L1(b)₀),
      --                           DUP^L2(DUP^L1(a)₁, DUP^L1(b)₁))
      ReduceM.modifyStats (·.incDupSupCommutation)
      let dupA ← ReduceM.addNode (.dup label) valEntry.ty
      let dupB ← ReduceM.addNode (.dup label) valEntry.ty
      let dup0 ← ReduceM.addNode (.dup innerLabel) valEntry.ty
      let dup1 ← ReduceM.addNode (.dup innerLabel) valEntry.ty
      -- Wire DUP_A to value a (inner DUP.copy0): fresh dupA replaces inner's endpoint
      ReduceM.rewirePort ⟨valId, ⟨1⟩⟩ (PortId.principal dupA)
      -- Wire DUP_B to value b (inner DUP.copy1): fresh dupB replaces inner's endpoint
      ReduceM.rewirePort ⟨valId, ⟨2⟩⟩ (PortId.principal dupB)
      -- Wire DUP_A outputs to DUP0.copy0 and DUP1.copy0
      ReduceM.connect ⟨dupA, ⟨1⟩⟩ ⟨dup0, ⟨1⟩⟩
      ReduceM.connect ⟨dupA, ⟨2⟩⟩ ⟨dup1, ⟨1⟩⟩
      -- Wire DUP_B outputs to DUP0.copy1 and DUP1.copy1
      ReduceM.connect ⟨dupB, ⟨1⟩⟩ ⟨dup0, ⟨2⟩⟩
      ReduceM.connect ⟨dupB, ⟨2⟩⟩ ⟨dup1, ⟨2⟩⟩
      -- Wire new DUPs to outer DUP's consumers
      ReduceM.rewirePort ⟨dupId, ⟨1⟩⟩ (PortId.principal dup0)
      ReduceM.rewirePort ⟨dupId, ⟨2⟩⟩ (PortId.principal dup1)
      ReduceM.disconnect (PortId.principal dupId)
      ReduceM.removeNode dupId
      ReduceM.removeNode valId
      ReduceM.trackPeakNodes
      whnf demandPort

  | other =>
    -- DUP-NOD: generic duplication for any node with auxiliary ports.
    -- Creates two copies of the node and recursively DUPs each aux port.
    -- Handles: CTOR, RECORD, STRING, ARRAY, SLICE, APP, OP1, OP2, MAT, PROJ,
    -- USE, INDEX, and any future node types with fields.
    -- Nodes with 0 aux ports (REF, ALO) are treated as flat copies.
    let arity := other.numAuxPorts
    if arity == 0 then
      -- Zero-arity node: flat copy (same as DUP-NUM but for REF/ALO)
      ReduceM.modifyStats (·.incDupCommutation)
      let copy0 ← ReduceM.addNode other valEntry.ty
      let copy1 ← ReduceM.addNode other valEntry.ty
      ReduceM.rewirePort ⟨dupId, ⟨1⟩⟩ (PortId.principal copy0)
      ReduceM.rewirePort ⟨dupId, ⟨2⟩⟩ (PortId.principal copy1)
      ReduceM.disconnect (PortId.principal dupId)
      ReduceM.removeNode dupId
      ReduceM.removeNode valId
      ReduceM.trackPeakNodes
      whnf demandPort
    else
      -- N-arity node: duplicate the node, DUP each auxiliary port
      ReduceM.modifyStats (·.incDupCommutation)
      let node0 ← ReduceM.addNode other valEntry.ty
      let node1 ← ReduceM.addNode other valEntry.ty
      for i in [:arity] do
        let dupField ← ReduceM.addNode (.dup label) valEntry.ty
        ReduceM.rewirePort ⟨valId, ⟨i + 1⟩⟩ (PortId.principal dupField)
        ReduceM.connect ⟨dupField, ⟨1⟩⟩ ⟨node0, ⟨i + 1⟩⟩
        ReduceM.connect ⟨dupField, ⟨2⟩⟩ ⟨node1, ⟨i + 1⟩⟩
      ReduceM.rewirePort ⟨dupId, ⟨1⟩⟩ (PortId.principal node0)
      ReduceM.rewirePort ⟨dupId, ⟨2⟩⟩ (PortId.principal node1)
      ReduceM.disconnect (PortId.principal dupId)
      ReduceM.removeNode dupId
      ReduceM.removeNode valId
      ReduceM.trackPeakNodes
      whnf demandPort

/-- Evaluate a port to weak head normal form.
    Returns the NodeId of the value node in WHNF.
    May modify the graph through interaction rules (β-reduction, etc.). -/
partial def whnf (demandPort : PortId) : ReduceM NodeId := do
  ReduceM.consumeFuel
  let target ← ReduceM.follow demandPort
  let entry ← ReduceM.getNode target.node
  if target.port.isPrincipal then
    whnfAtPrincipal target.node entry demandPort
  else
    whnfAtAuxiliary target.node entry target.port demandPort

/-- Handle evaluation when we arrive at a node's principal port.
    The node is "in head position" producing a value. -/
partial def whnfAtPrincipal (nid : NodeId) (entry : NodeEntry) (demandPort : PortId)
    : ReduceM NodeId := do
  match entry.node with
  -- Value nodes: already in WHNF
  | .num _ _ | .lam _ | .ctor _ _ | .record _ | .string | .array _
  | .sup _ | .slice | .era =>
    pure nid

  -- Application: evaluate function and possibly β-reduce
  | .app => do
    ReduceM.consumeFuel
    -- Evaluate the function (APP.aux0 = port 1)
    let fnId ← whnf ⟨nid, ⟨1⟩⟩
    let fnEntry ← ReduceM.getNode fnId
    match fnEntry.node with
    | .lam erased =>
      -- β-reduction: APP-LAM annihilation
      -- Both APP and LAM ports have existing connections: link bypasses both
      ReduceM.modifyStats (·.incBeta)
      if !erased then
        -- Bind argument to variable: APP.arg ↔ LAM.var
        ReduceM.link ⟨nid, ⟨2⟩⟩ ⟨fnId, ⟨1⟩⟩
      else
        -- Argument is unused: erase it
        erasePort ⟨nid, ⟨2⟩⟩
        ReduceM.disconnect ⟨fnId, ⟨1⟩⟩
      -- Link result to body: APP.principal ↔ LAM.body
      ReduceM.link ⟨nid, .principal⟩ ⟨fnId, ⟨2⟩⟩
      -- Clean up the APP-LAM connection
      ReduceM.disconnect ⟨nid, ⟨1⟩⟩
      ReduceM.removeNode nid
      ReduceM.removeNode fnId
      ReduceM.trackPeakNodes
      -- Re-evaluate: the body may need further reduction
      whnf demandPort

    | .sup supLabel =>
      -- APP-SUP: (&L{f,g} a) → !A &L = a; &L{(f A₀),(g A₁)}
      -- Distribute application through both branches of the superposition
      ReduceM.modifyStats (·.incSupCommutation)
      -- Create a DUP to clone the argument for both branches
      let dupArg ← ReduceM.addNode (.dup supLabel) fnEntry.ty
      ReduceM.rewirePort ⟨nid, ⟨2⟩⟩ (PortId.principal dupArg)
      -- Create two APP nodes: one for each SUP branch
      let app0 ← ReduceM.addNode .app entry.ty
      let app1 ← ReduceM.addNode .app entry.ty
      -- Wire SUP.val0 → APP0.fun, SUP.val1 → APP1.fun
      ReduceM.rewirePort ⟨fnId, ⟨1⟩⟩ ⟨app0, ⟨1⟩⟩
      ReduceM.rewirePort ⟨fnId, ⟨2⟩⟩ ⟨app1, ⟨1⟩⟩
      -- Wire DUP copies → APP args
      ReduceM.connect ⟨dupArg, ⟨1⟩⟩ ⟨app0, ⟨2⟩⟩
      ReduceM.connect ⟨dupArg, ⟨2⟩⟩ ⟨app1, ⟨2⟩⟩
      -- Create result SUP and wire APP results into it
      let resSup ← ReduceM.addNode (.sup supLabel) entry.ty
      ReduceM.connect (PortId.principal app0) ⟨resSup, ⟨1⟩⟩
      ReduceM.connect (PortId.principal app1) ⟨resSup, ⟨2⟩⟩
      -- Wire result SUP to APP's consumer
      ReduceM.rewirePort ⟨nid, .principal⟩ (PortId.principal resSup)
      -- Clean up original APP and SUP
      ReduceM.disconnect ⟨nid, ⟨1⟩⟩
      ReduceM.removeNode nid
      ReduceM.removeNode fnId
      ReduceM.trackPeakNodes
      whnf demandPort

    | .era =>
      -- APP-ERA: (ERA a) → ERA
      -- Erased function absorbs the application; argument is also erased
      ReduceM.modifyStats (·.incEraAbsorption)
      erasePort ⟨nid, ⟨2⟩⟩  -- erase argument
      -- Replace APP with ERA for its consumer
      let eraResult ← ReduceM.addNode .era
      ReduceM.rewirePort ⟨nid, .principal⟩ (PortId.principal eraResult)
      ReduceM.disconnect ⟨nid, ⟨1⟩⟩
      ReduceM.removeNode nid
      ReduceM.removeNode fnId
      whnf demandPort

    | _ =>
      -- Non-lambda/sup/era in function position: stuck application
      pure nid

  -- Binary operation: two-phase evaluation (left first, then right)
  | .op2 op => do
    ReduceM.consumeFuel
    -- Phase 1: evaluate left operand
    let leftId ← whnf ⟨nid, ⟨1⟩⟩
    let leftEntry ← ReduceM.getNode leftId
    match leftEntry.node with
    | .era =>
      -- OP2-ERA (left): (op ERA y) → ERA
      ReduceM.modifyStats (·.incEraAbsorption)
      erasePort ⟨nid, ⟨2⟩⟩
      let eraResult ← ReduceM.addNode .era
      ReduceM.rewirePort ⟨nid, .principal⟩ (PortId.principal eraResult)
      ReduceM.disconnect ⟨nid, ⟨1⟩⟩
      ReduceM.removeNode nid
      ReduceM.removeNode leftId
      whnf demandPort
    | .sup supLabel =>
      -- OP2-SUP (left): (op &L{a,b} y) → !Y &L = y; &L{(op a Y₀),(op b Y₁)}
      ReduceM.modifyStats (·.incSupCommutation)
      let dupRight ← ReduceM.addNode (.dup supLabel) entry.ty
      ReduceM.rewirePort ⟨nid, ⟨2⟩⟩ (PortId.principal dupRight)
      let op0 ← ReduceM.addNode (.op2 op) entry.ty
      let op1 ← ReduceM.addNode (.op2 op) entry.ty
      -- Wire SUP branches to OP2 left operands
      ReduceM.rewirePort ⟨leftId, ⟨1⟩⟩ ⟨op0, ⟨1⟩⟩
      ReduceM.rewirePort ⟨leftId, ⟨2⟩⟩ ⟨op1, ⟨1⟩⟩
      -- Wire DUP copies to OP2 right operands
      ReduceM.connect ⟨dupRight, ⟨1⟩⟩ ⟨op0, ⟨2⟩⟩
      ReduceM.connect ⟨dupRight, ⟨2⟩⟩ ⟨op1, ⟨2⟩⟩
      -- Create result SUP
      let resSup ← ReduceM.addNode (.sup supLabel) entry.ty
      ReduceM.connect (PortId.principal op0) ⟨resSup, ⟨1⟩⟩
      ReduceM.connect (PortId.principal op1) ⟨resSup, ⟨2⟩⟩
      ReduceM.rewirePort ⟨nid, .principal⟩ (PortId.principal resSup)
      ReduceM.disconnect ⟨nid, ⟨1⟩⟩
      ReduceM.removeNode nid
      ReduceM.removeNode leftId
      ReduceM.trackPeakNodes
      whnf demandPort
    | .num ptL vL =>
      -- Phase 2: left is NUM, evaluate right operand
      let rightId ← whnf ⟨nid, ⟨2⟩⟩
      let rightEntry ← ReduceM.getNode rightId
      match rightEntry.node with
      | .era =>
        -- OP2-ERA (right): (op #x ERA) → ERA
        ReduceM.modifyStats (·.incEraAbsorption)
        let eraResult ← ReduceM.addNode .era
        ReduceM.rewirePort ⟨nid, .principal⟩ (PortId.principal eraResult)
        ReduceM.disconnect ⟨nid, ⟨1⟩⟩
        ReduceM.disconnect ⟨nid, ⟨2⟩⟩
        ReduceM.removeNode nid
        ReduceM.removeNode leftId
        ReduceM.removeNode rightId
        whnf demandPort
      | .sup supLabel =>
        -- OP2-NUM-SUP (right): (op #x &L{a,b}) → &L{(op #x a),(op #x b)}
        -- NUM is flat: create two copies instead of DUP
        ReduceM.modifyStats (·.incSupCommutation)
        let numCopy0 ← ReduceM.addNode (.num ptL vL) leftEntry.ty
        let numCopy1 ← ReduceM.addNode (.num ptL vL) leftEntry.ty
        let op0 ← ReduceM.addNode (.op2 op) entry.ty
        let op1 ← ReduceM.addNode (.op2 op) entry.ty
        ReduceM.connect (PortId.principal numCopy0) ⟨op0, ⟨1⟩⟩
        ReduceM.connect (PortId.principal numCopy1) ⟨op1, ⟨1⟩⟩
        ReduceM.rewirePort ⟨rightId, ⟨1⟩⟩ ⟨op0, ⟨2⟩⟩
        ReduceM.rewirePort ⟨rightId, ⟨2⟩⟩ ⟨op1, ⟨2⟩⟩
        let resSup ← ReduceM.addNode (.sup supLabel) entry.ty
        ReduceM.connect (PortId.principal op0) ⟨resSup, ⟨1⟩⟩
        ReduceM.connect (PortId.principal op1) ⟨resSup, ⟨2⟩⟩
        ReduceM.rewirePort ⟨nid, .principal⟩ (PortId.principal resSup)
        ReduceM.disconnect ⟨nid, ⟨1⟩⟩
        ReduceM.disconnect ⟨nid, ⟨2⟩⟩
        ReduceM.removeNode nid
        ReduceM.removeNode leftId
        ReduceM.removeNode rightId
        ReduceM.trackPeakNodes
        whnf demandPort
      | .num _ptR vR =>
        -- OP2-NUM-NUM: both operands are numeric, compute result
        ReduceM.modifyStats (·.incArithmetic)
        match computeOp2 op vL vR with
        | .ok result =>
          let (resPt, resTy) := match op with
            | .eq | .ne | .lt | .le | .gt | .ge => (PrimType.bool, Value.vPrimTy .bool)
            | _ => (ptL, leftEntry.ty)
          let resultNode ← ReduceM.addNode (.num resPt result) resTy
          ReduceM.rewirePort ⟨nid, .principal⟩ (PortId.principal resultNode)
          ReduceM.disconnect ⟨nid, ⟨1⟩⟩
          ReduceM.disconnect ⟨nid, ⟨2⟩⟩
          ReduceM.removeNode nid
          ReduceM.removeNode leftId
          ReduceM.removeNode rightId
          whnf demandPort
        | .error e => throw e
      | _ =>
        -- Right operand stuck: check algebraic identities with left as constant
        match algebraicSimplify? op vL true with
        | some .identity =>
          ReduceM.modifyStats (·.incArithmetic)
          ReduceM.link ⟨nid, .principal⟩ ⟨nid, ⟨2⟩⟩
          ReduceM.disconnect ⟨nid, ⟨1⟩⟩
          ReduceM.removeNode nid
          ReduceM.removeNode leftId
          whnf demandPort
        | some (.absorb absorbVal) =>
          ReduceM.modifyStats (·.incArithmetic)
          erasePort ⟨nid, ⟨2⟩⟩
          let resultNode ← ReduceM.addNode (.num ptL absorbVal) leftEntry.ty
          ReduceM.rewirePort ⟨nid, .principal⟩ (PortId.principal resultNode)
          ReduceM.disconnect ⟨nid, ⟨1⟩⟩
          ReduceM.removeNode nid
          ReduceM.removeNode leftId
          whnf demandPort
        | none => pure nid
    | _ =>
      -- Left operand stuck: speculatively evaluate right for algebraic identity
      let rightId ← whnf ⟨nid, ⟨2⟩⟩
      let rightEntry ← ReduceM.getNode rightId
      match rightEntry.node with
      | .num ptR vR =>
        match algebraicSimplify? op vR false with
        | some .identity =>
          ReduceM.modifyStats (·.incArithmetic)
          ReduceM.link ⟨nid, .principal⟩ ⟨nid, ⟨1⟩⟩
          ReduceM.disconnect ⟨nid, ⟨2⟩⟩
          ReduceM.removeNode nid
          ReduceM.removeNode rightId
          whnf demandPort
        | some (.absorb absorbVal) =>
          ReduceM.modifyStats (·.incArithmetic)
          erasePort ⟨nid, ⟨1⟩⟩
          let resultNode ← ReduceM.addNode (.num ptR absorbVal) rightEntry.ty
          ReduceM.rewirePort ⟨nid, .principal⟩ (PortId.principal resultNode)
          ReduceM.disconnect ⟨nid, ⟨2⟩⟩
          ReduceM.removeNode nid
          ReduceM.removeNode rightId
          whnf demandPort
        | none => pure nid
      | _ => pure nid

  -- Unary operation
  | .op1 op => do
    ReduceM.consumeFuel
    let operandId ← whnf ⟨nid, ⟨1⟩⟩
    let operandEntry ← ReduceM.getNode operandId
    match operandEntry.node with
    | .era =>
      -- OP1-ERA: (op ERA) → ERA
      ReduceM.modifyStats (·.incEraAbsorption)
      let eraResult ← ReduceM.addNode .era
      ReduceM.rewirePort ⟨nid, .principal⟩ (PortId.principal eraResult)
      ReduceM.disconnect ⟨nid, ⟨1⟩⟩
      ReduceM.removeNode nid
      ReduceM.removeNode operandId
      whnf demandPort
    | .sup supLabel =>
      -- OP1-SUP: (op &L{a,b}) → &L{(op a),(op b)}
      ReduceM.modifyStats (·.incSupCommutation)
      let op0 ← ReduceM.addNode (.op1 op) entry.ty
      let op1 ← ReduceM.addNode (.op1 op) entry.ty
      ReduceM.rewirePort ⟨operandId, ⟨1⟩⟩ ⟨op0, ⟨1⟩⟩
      ReduceM.rewirePort ⟨operandId, ⟨2⟩⟩ ⟨op1, ⟨1⟩⟩
      let resSup ← ReduceM.addNode (.sup supLabel) entry.ty
      ReduceM.connect (PortId.principal op0) ⟨resSup, ⟨1⟩⟩
      ReduceM.connect (PortId.principal op1) ⟨resSup, ⟨2⟩⟩
      ReduceM.rewirePort ⟨nid, .principal⟩ (PortId.principal resSup)
      ReduceM.disconnect ⟨nid, ⟨1⟩⟩
      ReduceM.removeNode nid
      ReduceM.removeNode operandId
      ReduceM.trackPeakNodes
      whnf demandPort
    | .num pt v =>
      ReduceM.modifyStats (·.incArithmetic)
      let result := computeOp1 op v
      let resPt := match op with
        | .not => PrimType.bool
        | .neg => pt
      let resultNode ← ReduceM.addNode (.num resPt result) operandEntry.ty
      ReduceM.rewirePort ⟨nid, .principal⟩ (PortId.principal resultNode)
      ReduceM.disconnect ⟨nid, ⟨1⟩⟩
      ReduceM.removeNode nid
      ReduceM.removeNode operandId
      whnf demandPort
    | _ => pure nid  -- stuck

  -- Pattern match
  | .mat expectedTag => do
    ReduceM.consumeFuel
    let scrutId ← whnf ⟨nid, ⟨1⟩⟩
    let scrutEntry ← ReduceM.getNode scrutId
    match scrutEntry.node with
    | .era =>
      -- MAT-ERA: (mat ERA hit miss) → ERA
      ReduceM.modifyStats (·.incEraAbsorption)
      erasePort ⟨nid, ⟨2⟩⟩  -- erase hit
      erasePort ⟨nid, ⟨3⟩⟩  -- erase miss
      let eraResult ← ReduceM.addNode .era
      ReduceM.rewirePort ⟨nid, .principal⟩ (PortId.principal eraResult)
      ReduceM.disconnect ⟨nid, ⟨1⟩⟩
      ReduceM.removeNode nid
      ReduceM.removeNode scrutId
      whnf demandPort
    | .sup supLabel =>
      -- MAT-SUP: (mat &L{a,b} hit miss) → !H &L = hit; !M &L = miss;
      --          &L{(mat a H₀ M₀),(mat b H₁ M₁)}
      ReduceM.modifyStats (·.incSupCommutation)
      -- DUP both hit and miss branches
      let dupHit ← ReduceM.addNode (.dup supLabel) entry.ty
      let dupMiss ← ReduceM.addNode (.dup supLabel) entry.ty
      ReduceM.rewirePort ⟨nid, ⟨2⟩⟩ (PortId.principal dupHit)
      ReduceM.rewirePort ⟨nid, ⟨3⟩⟩ (PortId.principal dupMiss)
      -- Create two MAT nodes
      let mat0 ← ReduceM.addNode (.mat expectedTag) entry.ty
      let mat1 ← ReduceM.addNode (.mat expectedTag) entry.ty
      -- Wire SUP branches to MAT scrutinees
      ReduceM.rewirePort ⟨scrutId, ⟨1⟩⟩ ⟨mat0, ⟨1⟩⟩
      ReduceM.rewirePort ⟨scrutId, ⟨2⟩⟩ ⟨mat1, ⟨1⟩⟩
      -- Wire DUP copies to MAT hit/miss
      ReduceM.connect ⟨dupHit, ⟨1⟩⟩ ⟨mat0, ⟨2⟩⟩
      ReduceM.connect ⟨dupHit, ⟨2⟩⟩ ⟨mat1, ⟨2⟩⟩
      ReduceM.connect ⟨dupMiss, ⟨1⟩⟩ ⟨mat0, ⟨3⟩⟩
      ReduceM.connect ⟨dupMiss, ⟨2⟩⟩ ⟨mat1, ⟨3⟩⟩
      -- Create result SUP
      let resSup ← ReduceM.addNode (.sup supLabel) entry.ty
      ReduceM.connect (PortId.principal mat0) ⟨resSup, ⟨1⟩⟩
      ReduceM.connect (PortId.principal mat1) ⟨resSup, ⟨2⟩⟩
      ReduceM.rewirePort ⟨nid, .principal⟩ (PortId.principal resSup)
      ReduceM.disconnect ⟨nid, ⟨1⟩⟩
      ReduceM.removeNode nid
      ReduceM.removeNode scrutId
      ReduceM.trackPeakNodes
      whnf demandPort
    | .ctor tag _arity =>
      ReduceM.modifyStats (·.incMatch)
      if tag == expectedTag then
        ReduceM.link ⟨nid, .principal⟩ ⟨nid, ⟨2⟩⟩
        erasePort ⟨nid, ⟨3⟩⟩
      else
        ReduceM.link ⟨nid, .principal⟩ ⟨nid, ⟨3⟩⟩
        erasePort ⟨nid, ⟨2⟩⟩
      erasePort ⟨nid, ⟨1⟩⟩
      ReduceM.removeNode nid
      whnf demandPort
    | .num _ v =>
      ReduceM.modifyStats (·.incMatch)
      if v.toNat == expectedTag then
        ReduceM.link ⟨nid, .principal⟩ ⟨nid, ⟨2⟩⟩
        erasePort ⟨nid, ⟨3⟩⟩
      else
        ReduceM.link ⟨nid, .principal⟩ ⟨nid, ⟨3⟩⟩
        erasePort ⟨nid, ⟨2⟩⟩
      erasePort ⟨nid, ⟨1⟩⟩
      ReduceM.removeNode nid
      whnf demandPort
    | .array _ =>
      let lenId ← whnf ⟨scrutId, ⟨1⟩⟩
      let lenEntry ← ReduceM.getNode lenId
      match lenEntry.node with
      | .num _ v =>
        let isHit := if expectedTag == 0 then v.toNat == 0
                     else if expectedTag == 1 then v.toNat > 0
                     else false
        ReduceM.modifyStats (·.incMatch)
        if isHit then
          ReduceM.link ⟨nid, .principal⟩ ⟨nid, ⟨2⟩⟩
          erasePort ⟨nid, ⟨3⟩⟩
        else
          ReduceM.link ⟨nid, .principal⟩ ⟨nid, ⟨3⟩⟩
          erasePort ⟨nid, ⟨2⟩⟩
        erasePort ⟨nid, ⟨1⟩⟩
        ReduceM.removeNode nid
        whnf demandPort
      | _ => pure nid -- dynamic length, stuck
    | _ => pure nid  -- stuck

  -- Field projection
  | .proj fieldIdx => do
    ReduceM.consumeFuel
    let recId ← whnf ⟨nid, ⟨1⟩⟩
    let recEntry ← ReduceM.getNode recId
    match recEntry.node with
    | .era =>
      -- PROJ-ERA: (proj ERA) → ERA
      ReduceM.modifyStats (·.incEraAbsorption)
      let eraResult ← ReduceM.addNode .era
      ReduceM.rewirePort ⟨nid, .principal⟩ (PortId.principal eraResult)
      ReduceM.disconnect ⟨nid, ⟨1⟩⟩
      ReduceM.removeNode nid
      ReduceM.removeNode recId
      whnf demandPort
    | .sup supLabel =>
      -- PROJ-SUP: (proj_i &L{a,b}) → &L{(proj_i a),(proj_i b)}
      ReduceM.modifyStats (·.incSupCommutation)
      let proj0 ← ReduceM.addNode (.proj fieldIdx) entry.ty
      let proj1 ← ReduceM.addNode (.proj fieldIdx) entry.ty
      ReduceM.rewirePort ⟨recId, ⟨1⟩⟩ ⟨proj0, ⟨1⟩⟩
      ReduceM.rewirePort ⟨recId, ⟨2⟩⟩ ⟨proj1, ⟨1⟩⟩
      let resSup ← ReduceM.addNode (.sup supLabel) entry.ty
      ReduceM.connect (PortId.principal proj0) ⟨resSup, ⟨1⟩⟩
      ReduceM.connect (PortId.principal proj1) ⟨resSup, ⟨2⟩⟩
      ReduceM.rewirePort ⟨nid, .principal⟩ (PortId.principal resSup)
      ReduceM.disconnect ⟨nid, ⟨1⟩⟩
      ReduceM.removeNode nid
      ReduceM.removeNode recId
      ReduceM.trackPeakNodes
      whnf demandPort
    | .record numFields =>
      ReduceM.modifyStats (·.incProjection)
      ReduceM.link ⟨nid, .principal⟩ ⟨recId, ⟨fieldIdx + 1⟩⟩
      for i in [:numFields] do
        if i != fieldIdx then
          erasePort ⟨recId, ⟨i + 1⟩⟩
      ReduceM.disconnect ⟨nid, ⟨1⟩⟩
      ReduceM.removeNode nid
      ReduceM.removeNode recId
      whnf demandPort
    | .ctor _tag arity =>
      ReduceM.modifyStats (·.incProjection)
      ReduceM.link ⟨nid, .principal⟩ ⟨recId, ⟨fieldIdx + 1⟩⟩
      for i in [:arity] do
        if i != fieldIdx then
          erasePort ⟨recId, ⟨i + 1⟩⟩
      ReduceM.disconnect ⟨nid, ⟨1⟩⟩
      ReduceM.removeNode nid
      ReduceM.removeNode recId
      whnf demandPort
    | .array elemType =>
      ReduceM.modifyStats (·.incProjection)
      if fieldIdx == 0 then
        -- Head: extract first element from backing CTOR(0xFFFD)
        let dataId ← whnf ⟨recId, ⟨2⟩⟩
        let dataEntry ← ReduceM.getNode dataId
        match dataEntry.node with
        | .ctor _ arity =>
          -- Link result to CTOR's first field (aux port 1)
          ReduceM.link ⟨nid, .principal⟩ ⟨dataId, ⟨1⟩⟩
          -- Erase remaining CTOR fields
          for i in [1:arity] do
            erasePort ⟨dataId, ⟨i + 1⟩⟩
          -- Erase array's length
          erasePort ⟨recId, ⟨1⟩⟩
          -- Disconnect ARRAY from CTOR and PROJ from ARRAY
          ReduceM.disconnect ⟨recId, ⟨2⟩⟩
          ReduceM.disconnect ⟨nid, ⟨1⟩⟩
          ReduceM.removeNode nid
          ReduceM.removeNode dataId
          ReduceM.removeNode recId
          whnf demandPort
        | _ => pure nid
      else if fieldIdx == 1 then
        -- Tail: create new array with remaining elements (O(1) graph rewiring)
        let lenId ← whnf ⟨recId, ⟨1⟩⟩
        let lenEntry ← ReduceM.getNode lenId
        let dataId ← whnf ⟨recId, ⟨2⟩⟩
        let dataEntry ← ReduceM.getNode dataId
        match lenEntry.node, dataEntry.node with
        | .num pt v, .ctor _ arity =>
          let newLen := v - 1
          let newArity := arity - 1
          -- Create new length NUM
          let newLenNode ← ReduceM.addNode (.num pt newLen) lenEntry.ty
          let newDataNode ← ReduceM.addNode (.ctor 0xFFFD newArity) recEntry.ty
          for i in [:newArity] do
            ReduceM.rewirePort ⟨dataId, ⟨i + 2⟩⟩ ⟨newDataNode, ⟨i + 1⟩⟩
          erasePort ⟨dataId, ⟨1⟩⟩
          -- Create new ARRAY node
          let newArrayNode ← ReduceM.addNode (.array elemType) recEntry.ty
          ReduceM.connect ⟨newArrayNode, ⟨1⟩⟩ (PortId.principal newLenNode)
          ReduceM.connect ⟨newArrayNode, ⟨2⟩⟩ (PortId.principal newDataNode)
          -- Rewire demand to new array
          ReduceM.rewirePort ⟨nid, .principal⟩ (PortId.principal newArrayNode)
          -- Clean up old nodes
          ReduceM.disconnect ⟨recId, ⟨1⟩⟩
          ReduceM.disconnect ⟨recId, ⟨2⟩⟩
          ReduceM.disconnect ⟨nid, ⟨1⟩⟩
          ReduceM.removeNode nid
          ReduceM.removeNode dataId
          ReduceM.removeNode lenId
          ReduceM.removeNode recId
          ReduceM.trackPeakNodes
          whnf demandPort
        | _, _ => pure nid
      else pure nid
    | _ => pure nid  -- stuck

  -- Definition instantiation (ALO)
  | .alo refId => do
    ReduceM.consumeFuel
    let def_ ← ReduceM.getDefinition refId
    if def_.isExternal then
      pure nid
    else if (← ReduceM.isNormalizingDef refId) then
      pure nid
    else
      ReduceM.modifyStats (·.incInstantiation)
      -- Deep-copy the definition's subgraph
      let rootCopy ← copySubgraph def_.root
      -- Rewire: ALO's consumer now gets the instantiated root
      let aloConsumer ← ReduceM.getConnection (PortId.principal nid)
      ReduceM.disconnect (PortId.principal nid)
      match aloConsumer with
      | some consumer => ReduceM.connect consumer rootCopy
      | none => pure ()
      ReduceM.removeNode nid
      ReduceM.trackPeakNodes
      whnf demandPort

  -- Global reference: convert to ALO for instantiation
  | .ref refId => do
    ReduceM.consumeFuel
    let def_ ← ReduceM.getDefinition refId
    if def_.isExternal then
      pure nid
    else if (← ReduceM.isNormalizingDef refId) then
      pure nid
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
      whnf demandPort

  -- Strict evaluation (USE): force the term for side effects, return continuation.
  -- USE implements CBV sequencing: evaluate the term to WHNF (executing any side
  -- effects), then discard the term and return the continuation's value.
  -- If the term is stuck, USE remains in the graph so the Alloy lowering can emit the call before the continuation.
  | .use => do
    ReduceM.consumeFuel
    -- Force the term to WHNF
    let termId ← whnf ⟨nid, ⟨1⟩⟩
    let termEntry ← ReduceM.getNode termId
    match termEntry.node with
    | .num _ _ | .era | .ctor _ _ | .record _ | .string | .array _ | .lam _ | .sup _ =>
      ReduceM.modifyStats (·.incUse)
      erasePort ⟨nid, ⟨1⟩⟩
      ReduceM.link ⟨nid, .principal⟩ ⟨nid, ⟨2⟩⟩
      ReduceM.removeNode nid
      whnf demandPort
    | _ => pure nid

  -- DUP at principal shouldn't be reached in demand-driven evaluation
  -- (we always arrive at DUP from its auxiliary ports)
  | .dup _ | .index => pure nid

/-- Handle evaluation when we arrive at a node's auxiliary port.
    This occurs when following a wire from a consumer into a DUP chain. -/
partial def whnfAtAuxiliary (nid : NodeId) (entry : NodeEntry) (_port : PortIdx)
    (demandPort : PortId) : ReduceM NodeId := do
  match entry.node with
  | .dup label =>
    -- Consumer wants a copy from this DUP node
    resolveDup nid label demandPort
  | _ =>
    -- Arriving at an auxiliary port of other node types:
    -- This means we're looking "backwards" through the graph.
    -- This is a stuck term (e.g., free variable).
    pure nid

end -- mutual

end Somac.Circuit.Reduce
