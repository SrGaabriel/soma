import Somac.Circuit.Reduce.Interact

namespace Somac.Circuit.Reduce

open Somac.Circuit.Node (Node NodeId PortId PortIdx)

/-- Normalize safe sub-expressions of a node after WHNF -/
def nfChildren (recurse : PortId → ReduceM NodeId)
    (nid : NodeId) (node : Node) : ReduceM Unit := do
  match node with
  -- Closure CTORs: the function LAM will be extracted as a separate Alloy definition
  | .ctor tag 2 =>
    if tag == 0xFFFE then pure ()
    else
      let _ ← recurse ⟨nid, ⟨1⟩⟩; let _ ← recurse ⟨nid, ⟨2⟩⟩; pure ()
  -- Data nodes: all fields (tree-structured, no recursive refs)
  | .ctor _ arity =>
    for i in [:arity] do let _ ← recurse ⟨nid, ⟨i + 1⟩⟩
  | .record n =>
    for i in [:n] do let _ ← recurse ⟨nid, ⟨i + 1⟩⟩
  | .sup _ | .array _ | .string =>
    let _ ← recurse ⟨nid, ⟨1⟩⟩; let _ ← recurse ⟨nid, ⟨2⟩⟩; pure ()
  | .slice =>
    let _ ← recurse ⟨nid, ⟨1⟩⟩; let _ ← recurse ⟨nid, ⟨2⟩⟩
    let _ ← recurse ⟨nid, ⟨3⟩⟩; pure ()
  -- Stuck computations: normalize operands/arguments
  | .app | .op2 _ =>
    let _ ← recurse ⟨nid, ⟨1⟩⟩; let _ ← recurse ⟨nid, ⟨2⟩⟩; pure ()
  | .op1 _ | .proj _ =>
    let _ ← recurse ⟨nid, ⟨1⟩⟩; pure ()
  -- Erased LAM: var connects to ERA (no DUP cycle), body normalization is safe
  | .lam true =>
    let _ ← recurse ⟨nid, ⟨2⟩⟩; pure ()
  -- Non-erased LAM: only safe if var is used linearly (no DUP)
  | .lam false => do
    match ← ReduceM.getConnection ⟨nid, ⟨1⟩⟩ with
    | some target =>
      let varEntry ← ReduceM.getNode target.node
      match varEntry.node with
      | .dup _ => pure ()
      | _ => let _ ← recurse ⟨nid, ⟨2⟩⟩; pure ()
    | none => pure ()
  -- Stuck MAT: scrutinee was already WHNF'd so we can normalize all sub-expressions!
  -- Safe because normalizingDefs guards prevent infinite recursive instantiation
  | .mat _ =>
    let _ ← recurse ⟨nid, ⟨1⟩⟩
    let _ ← recurse ⟨nid, ⟨2⟩⟩
    let _ ← recurse ⟨nid, ⟨3⟩⟩
    pure ()
  -- Terminal: DUP (consumers), NUM/ERA/REF/ALO (leaves)
  | _ => pure ()

/-- Try eta-reduction: λx. f x → f -/
def tryEtaReduce (nid : NodeId) : ReduceM Bool := do
  -- LAM.var (port 1) must connect to APP.arg (port 2) of some APP
  let some varTarget ← ReduceM.getConnection ⟨nid, ⟨1⟩⟩ | return false
  if varTarget.port.idx != 2 then return false
  let varEntry ← ReduceM.getNode varTarget.node
  match varEntry.node with
  | .app => pure ()
  | _ => return false
  -- LAM.body (port 2) must connect to the same APP's principal (port 0)
  let some bodyTarget ← ReduceM.getConnection ⟨nid, ⟨2⟩⟩ | return false
  if bodyTarget.node != varTarget.node || !bodyTarget.port.isPrincipal then return false
  -- APP.function (port 1) is what the consumer would receive after eta-reduction.
  let appId := varTarget.node
  let some fnTarget ← ReduceM.getConnection ⟨appId, ⟨1⟩⟩ | return false
  let fnEntry ← ReduceM.getNode fnTarget.node
  if fnTarget.port.isPrincipal then
    match fnEntry.node with
    | .app =>
      -- Check whether the APP is reducible or a stuck partial application
      let some appFnTarget ← ReduceM.getConnection ⟨fnTarget.node, ⟨1⟩⟩ | return false
      let appFnEntry ← ReduceM.getNode appFnTarget.node
      match appFnEntry.node with
      | .lam _ | .ctor _ _ =>
        -- Beta-redex or constructor application so it will reduce further, safe to eta
        pure ()
      | _ =>
        -- Potentially stuck partial application
        return false
    | _ => pure ()
  -- Safe to eta-reduce: λx. f x → f
  ReduceM.modifyStats (·.incEta)
  ReduceM.link ⟨nid, .principal⟩ ⟨appId, ⟨1⟩⟩
  ReduceM.disconnect ⟨nid, ⟨1⟩⟩
  ReduceM.disconnect ⟨nid, ⟨2⟩⟩
  ReduceM.removeNode nid
  ReduceM.removeNode appId
  return true

/-- Evaluate to full normal form: reduce to WHNF, then recursively normalize safe sub-expressions -/
partial def nf (demandPort : PortId) : ReduceM NodeId := do
  let nid ← whnf demandPort
  let target ← ReduceM.follow demandPort
  if target.port.isPrincipal then
    let entry ← ReduceM.getNode nid
    match entry.node with
    | .lam false =>
      if (← tryEtaReduce nid) then
        return ← nf demandPort
      else
        nfChildren nf nid entry.node
    | _ => nfChildren nf nid entry.node
  pure nid

end Somac.Circuit.Reduce
