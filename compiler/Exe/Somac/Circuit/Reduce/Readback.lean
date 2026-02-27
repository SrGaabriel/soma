import Somac.Circuit.Reduce.Types
import Somac.Circuit.Reduce.Interact
import Somac.Circuit.Graph
import Somac.Circuit.Node
import Somac.Circuit.Term
import Soma.Core.Value

namespace Somac.Circuit.Reduce

open Somac.Circuit.Graph (Graph NodeEntry)
open Somac.Circuit.Node (Node NodeId PortId PortIdx Label)
open Somac.Circuit.Term (PrimType)

/-- Readback state: tracks visited nodes to prevent cycles -/
structure ReadbackCtx where
  visited : Std.HashSet Nat := {}
  /-- String table for resolving string literals -/
  stringTable : Array String := #[]
  /-- Maximum readback depth -/
  maxDepth : Nat := 1000

mutual

/-- Read back a value from a port in the graph, following wires -/
partial def readbackPort (port : PortId) (ctx : ReadbackCtx) (depth : Nat := 0)
    : ReduceM ReadbackValue := do
  if depth > ctx.maxDepth then
    return .stuck (.stuckApplication ⟨0⟩)

  -- Evaluate to WHNF first
  let nid ← whnf port
  readbackNode nid ctx depth

/-- Read back a value from a node that is already in WHNF -/
partial def readbackNode (nid : NodeId) (ctx : ReadbackCtx) (depth : Nat := 0)
    : ReduceM ReadbackValue := do
  -- Cycle detection
  if ctx.visited.contains nid.id then
    return .stuck (.stuckApplication nid)
  let ctx := { ctx with visited := ctx.visited.insert nid.id }

  let entry ← ReduceM.getNode nid
  match entry.node with
  | .num .bool v => return .num .bool v
  | .num pt v => return .num pt v

  | .era => return .erased

  | .lam erased => return .lam erased

  | .ctor tag arity =>
    -- Check for panic tag
    if tag == 0xFFFF then
      -- Panic node: extract message hash and line from fields
      if arity >= 2 then
        let field0 ← readbackPort ⟨nid, ⟨1⟩⟩ ctx (depth + 1)
        let field1 ← readbackPort ⟨nid, ⟨2⟩⟩ ctx (depth + 1)
        match field0, field1 with
        | .num _ msgHash, .num _ line =>
          throw (.panic msgHash line)
        | _, _ => throw (.panic 0 0)
      else
        throw (.panic 0 0)
    let mut fields : Array ReadbackValue := #[]
    for i in [:arity] do
      let field ← readbackPort ⟨nid, ⟨i + 1⟩⟩ ctx (depth + 1)
      fields := fields.push field
    return .ctor tag fields

  | .record numFields =>
    let mut fields : Array ReadbackValue := #[]
    for i in [:numFields] do
      let field ← readbackPort ⟨nid, ⟨i + 1⟩⟩ ctx (depth + 1)
      fields := fields.push field
    return .record fields

  | .sup label =>
    let v0 ← readbackPort ⟨nid, ⟨1⟩⟩ ctx (depth + 1)
    let v1 ← readbackPort ⟨nid, ⟨2⟩⟩ ctx (depth + 1)
    return .sup label v0 v1

  | .string =>
    -- Resolve from string table: data port (aux1) holds the string table index
    let dataTarget ← ReduceM.follow ⟨nid, ⟨2⟩⟩
    let dataEntry ← ReduceM.getNode dataTarget.node
    match dataEntry.node with
    | .num _ idx =>
      let strIdx := idx.toNat
      if h : strIdx < ctx.stringTable.size then
        return .string ctx.stringTable[strIdx]
      else
        return .string s!"<string@{strIdx}>"
    | _ => return .string "<unresolved>"

  | .array elemType =>
    -- Read array: data port (aux1) holds a CTOR containing elements
    let dataTarget ← ReduceM.follow ⟨nid, ⟨2⟩⟩
    let dataEntry ← ReduceM.getNode dataTarget.node
    match dataEntry.node with
    | .ctor _ arity =>
      let mut elems : Array ReadbackValue := #[]
      for i in [:arity] do
        let elem ← readbackPort ⟨dataTarget.node, ⟨i + 1⟩⟩ ctx (depth + 1)
        elems := elems.push elem
      return .array elemType elems
    | _ => return .array elemType #[]

  -- Computation nodes that weren't reduced (stuck terms)
  | .app => return .stuck (.stuckApplication nid)
  | .op1 _ | .op2 _ => return .stuck (.stuckOperator nid)
  | .mat _ => return .stuck (.stuckMatch nid)
  | .proj _ => return .stuck (.stuckProjection nid)
  | .alo refId => do
    let def_ ← ReduceM.getDefinition refId
    if def_.isExternal then
      return .stuck (.externalFunction def_.name.display refId)
    else
      return .stuck (.stuckApplication nid)
  | .ref refId => do
    let def_ ← ReduceM.getDefinition refId
    return .stuck (.externalFunction def_.name.display refId)
  | .dup _ | .use | .index | .slice =>
    return .stuck (.stuckApplication nid)

end

/-- Read back the result from the graph's root port -/
def readbackRoot : ReduceM ReadbackValue := do
  let g ← ReduceM.getGraph
  let ctx : ReadbackCtx := { stringTable := g.getStringTable }
  readbackPort g.root ctx

end Somac.Circuit.Reduce
