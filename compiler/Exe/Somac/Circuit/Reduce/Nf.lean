import Somac.Circuit.Reduce.Interact

namespace Somac.Circuit.Reduce

open Somac.Circuit.Node (Node NodeId PortId PortIdx)

/-- Ports of a node that a depth-first normal-form walk should descend into after WHNF has settled the head -/
private def normalizationChildren (nid : NodeId) : Node → Array PortId
  | .ctor tag 2 =>
    if tag == 0xFFFE then #[]
    else #[⟨nid, ⟨1⟩⟩, ⟨nid, ⟨2⟩⟩]
  | .ctor _ arity =>
    Array.ofFn (n := arity) (fun i => ⟨nid, ⟨i.val + 1⟩⟩)
  | .record n =>
    Array.ofFn (n := n) (fun i => ⟨nid, ⟨i.val + 1⟩⟩)
  | .sup _ | .array _ | .string =>
    #[⟨nid, ⟨1⟩⟩, ⟨nid, ⟨2⟩⟩]
  | .slice =>
    #[⟨nid, ⟨1⟩⟩, ⟨nid, ⟨2⟩⟩, ⟨nid, ⟨3⟩⟩]
  | .app | .op2 _ =>
    #[⟨nid, ⟨1⟩⟩, ⟨nid, ⟨2⟩⟩]
  | .op1 _ | .proj _ =>
    #[⟨nid, ⟨1⟩⟩]
  | .lam _ =>
    #[⟨nid, ⟨2⟩⟩]
  | .mat _ =>
    #[⟨nid, ⟨1⟩⟩, ⟨nid, ⟨2⟩⟩, ⟨nid, ⟨3⟩⟩]
  | _ => #[]

/-- Iteratively evaluate a port to full normal form -/
partial def nf (initialPort : PortId) : ReduceM NodeId := do
  let mut workStack : Array PortId := #[initialPort]

  let mut visited : Std.HashSet Nat := {}
  while !workStack.isEmpty do
    let port := workStack.back!
    workStack := workStack.pop
    let nid ← whnf port
    if visited.contains nid.id then
      continue
    visited := visited.insert nid.id
    let target ← ReduceM.follow port
    if !target.port.isPrincipal then
      continue
    let entry ← ReduceM.getNode nid
    for child in normalizationChildren nid entry.node do
      workStack := workStack.push child
  whnf initialPort

end Somac.Circuit.Reduce
