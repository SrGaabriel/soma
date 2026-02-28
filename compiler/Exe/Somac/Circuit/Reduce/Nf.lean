import Somac.Circuit.Reduce.Interact

namespace Somac.Circuit.Reduce

open Somac.Circuit.Node (Node NodeId PortId PortIdx)

/-- Normalize safe sub-expressions of a node after WHNF -/
def nfChildren (recurse : PortId → ReduceM NodeId)
    (nid : NodeId) (node : Node) : ReduceM Unit := do
  match node with
  -- Lambda: body only (port 2). Port 1 connects into consumers.
  | .lam _ =>
    let _ ← recurse ⟨nid, ⟨2⟩⟩; pure ()
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
  -- Terminal: MAT (branches may recurse), DUP (consumers), NUM/ERA/REF/ALO (leaves)
  | _ => pure ()

/-- Evaluate to full normal form: reduce to WHNF, then recursively normalize safe sub-expressions -/
partial def nf (demandPort : PortId) : ReduceM NodeId := do
  let nid ← whnf demandPort
  let entry ← ReduceM.getNode nid
  nfChildren nf nid entry.node
  pure nid

end Somac.Circuit.Reduce
