import Somac.Circuit.Node
import Somac.Circuit.Term
import Soma.Core.Value
import Soma.Core.Expr
import Std.Data.HashMap

namespace Somac.Circuit.Graph

open Somac.Circuit.Node (Node NodeId PortId PortIdx Wire ActivePair Label)
open Somac.Circuit.Term (Term Tag Loc)
open Soma.Core (Value QualifiedName)

/-- Enumerate a list with indices -/
def enumList (xs : List α) : List (Nat × α) :=
  let rec go (i : Nat) : List α → List (Nat × α)
    | [] => []
    | x :: xs => (i, x) :: go (i + 1) xs
  go 0 xs

/-- An entry in the graph: a node with its connectivity and type -/
structure NodeEntry where
  /-- The node itself -/
  node : Node
  /-- Connections for each port (indexed by PortIdx) -/
  ports : Array (Option PortId)
  /-- Type of the value at the principal port (from elaboration) -/
  ty : Value
  deriving Inhabited

namespace NodeEntry

/-- Create an entry for a node with unconnected ports -/
def create (n : Node) (ty : Value) : NodeEntry :=
  { node := n
  , ports := Array.mk (List.replicate n.numPorts none)
  , ty := ty
  }

/-- Get the connection at a port index -/
def getPort (e : NodeEntry) (p : PortIdx) : Option PortId :=
  if h : p.idx < e.ports.size then e.ports[p.idx] else none

/-- Set the connection at a port index -/
def setPort (e : NodeEntry) (p : PortIdx) (target : PortId) : NodeEntry :=
  if p.idx < e.ports.size
  then { e with ports := e.ports.set! p.idx (some target) }
  else e

/-- Get the principal port connection -/
def getPrincipal (e : NodeEntry) : Option PortId :=
  e.getPort .principal

/-- Check if all ports are connected -/
def isFullyConnected (e : NodeEntry) : Bool :=
  e.ports.all Option.isSome

/-- Get all connected ports as a list -/
def connections (e : NodeEntry) : List (PortIdx × PortId) :=
  (enumList e.ports.toList).filterMap fun (i, opt) =>
    opt.map fun target => (⟨i⟩, target)

end NodeEntry

/-- A global definition in the "book" (for recursion via REF nodes) -/
structure Definition where
  /-- Unique name for this definition -/
  name : QualifiedName
  /-- The root node of the definition's graph -/
  root : NodeId
  /-- Parameter count (for lazy instantiation) -/
  arity : Nat
  /-- Full type of this definition (possibly polymorphic) -/
  ty : Value
  /-- Whether this is an external/intrinsic function -/
  isExternal : Bool := false
  deriving Inhabited

/-- The interaction net graph -/
structure Graph where
  /-- All nodes, indexed by NodeId -/
  nodes : Std.HashMap Nat NodeEntry
  /-- The root port (program output) -/
  root : PortId
  /-- Next available node ID -/
  nextId : Nat
  /-- Next available duplication label -/
  nextLabel : UInt32
  /-- Global definitions book (for REF nodes) -/
  book : Array Definition
  /-- String table: maps string content → index -/
  strings : Std.HashMap String Nat := {}
  /-- Next string index -/
  nextStringIdx : Nat := 0
  /-- Resolved type arguments per call site -/
  resolvedTypeArgs : Std.HashMap Nat (Array Value) := {}
  deriving Inhabited

namespace Graph

/-- Create an empty graph -/
def empty : Graph :=
  { nodes := {}
  , root := ⟨⟨0⟩, .principal⟩
  , nextId := 0
  , nextLabel := 0
  , book := #[]
  }

/-- Store resolved type arguments for a call site node -/
def setResolvedTypeArgs (g : Graph) (nodeId : NodeId) (typeArgs : Array Value) : Graph :=
  { g with resolvedTypeArgs := g.resolvedTypeArgs.insert nodeId.id typeArgs }

/-- Get resolved type arguments for a call site node -/
def getResolvedTypeArgs (g : Graph) (nodeId : NodeId) : Option (Array Value) :=
  g.resolvedTypeArgs.get? nodeId.id

/-- Allocate a fresh node ID -/
def freshNodeId (g : Graph) : NodeId × Graph :=
  (⟨g.nextId⟩, { g with nextId := g.nextId + 1 })

/-- Allocate a fresh duplication label -/
def freshLabel (g : Graph) : Label × Graph :=
  (⟨g.nextLabel⟩, { g with nextLabel := g.nextLabel + 1 })

/-- Intern a string, returning its index. If already interned, returns existing index -/
def internString (g : Graph) (s : String) : Nat × Graph :=
  match g.strings.get? s with
  | some idx => (idx, g)
  | none =>
    let idx := g.nextStringIdx
    (idx, { g with
      strings := g.strings.insert s idx
      nextStringIdx := idx + 1
    })

/-- Get all strings as an array ordered by index -/
def getStringTable (g : Graph) : Array String := Id.run do
  let mut arr : Array String := .mkEmpty g.nextStringIdx
  for _ in [:g.nextStringIdx] do
    arr := arr.push ""
  for (s, idx) in g.strings.toList do
    arr := arr.set! idx s
  arr

/-- Allocate N consecutive labels (for DUP chains) -/
def freshLabels (g : Graph) (n : Nat) : Array Label × Graph :=
  let labels := Array.range n |>.map fun i => Label.ofNat (g.nextLabel.toNat + i)
  (labels, { g with nextLabel := g.nextLabel + n.toUInt32 })

/-- Add a node to the graph -/
def addNode (g : Graph) (n : Node) (ty : Value) : NodeId × Graph :=
  let (nid, g') := g.freshNodeId
  let entry := NodeEntry.create n ty
  (nid, { g' with nodes := g'.nodes.insert nid.id entry })

/-- Add a node and immediately set its root as the graph root -/
def addRootNode (g : Graph) (n : Node) (ty : Value) : NodeId × Graph :=
  let (nid, g') := g.addNode n ty
  (nid, { g' with root := PortId.principal nid })

/-- Look up a node by ID -/
def getNode (g : Graph) (nid : NodeId) : Option NodeEntry :=
  g.nodes.get? nid.id

/-- Look up just the Node (not the entry) -/
def getNodeType (g : Graph) (nid : NodeId) : Option Node :=
  g.getNode nid |>.map (·.node)

/-- Update a node entry -/
def updateNode (g : Graph) (nid : NodeId) (f : NodeEntry → NodeEntry) : Graph :=
  match g.nodes.get? nid.id with
  | some entry => { g with nodes := g.nodes.insert nid.id (f entry) }
  | none => g

/-- Remove a node from the graph -/
def removeNode (g : Graph) (nid : NodeId) : Graph :=
  { g with nodes := g.nodes.erase nid.id }

/-- Connect two ports with a wire (bidirectional) -/
def connect (g : Graph) (p1 p2 : PortId) : Graph :=
  let g' := g.updateNode p1.node fun e => e.setPort p1.port p2
  g'.updateNode p2.node fun e => e.setPort p2.port p1

/-- Get what a port is connected to -/
def getConnection (g : Graph) (p : PortId) : Option PortId :=
  g.getNode p.node |>.bind fun e => e.getPort p.port

/-- Disconnect a port (set to unconnected) -/
def disconnect (g : Graph) (p : PortId) : Graph :=
  -- First, disconnect the other end
  let g' := match g.getConnection p with
    | some other => g.updateNode other.node fun e =>
        { e with ports := e.ports.modify other.port.idx (fun _ => none) }
    | none => g
  -- Then disconnect this end
  g'.updateNode p.node fun e =>
    { e with ports := e.ports.modify p.port.idx (fun _ => none) }

/-- Disconnect p1 from its current target and connect it to p2's target -/
def rewire (g : Graph) (p1 p2 : PortId) : Graph :=
  match g.getConnection p2 with
  | some target =>
    let g' := g.disconnect p1
    let g'' := g'.disconnect p2
    g''.connect p1 target
  | none => g

/-- Get all node IDs in the graph -/
def nodeIds (g : Graph) : List NodeId :=
  g.nodes.toList.map fun (id, _) => ⟨id⟩

/-- Count nodes in the graph -/
def nodeCount (g : Graph) : Nat :=
  g.nodes.size

/-- Get all wires in the graph (deduplicated) -/
def wires (g : Graph) : List Wire :=
  let allConnections := g.nodes.toList.flatMap fun (id, entry) =>
    entry.connections.filterMap fun (pIdx, target) =>
      -- Only include wire if this end has smaller ID (deduplication)
      let thisPort : PortId := ⟨⟨id⟩, pIdx⟩
      if id < target.node.id || (id == target.node.id && pIdx.idx < target.port.idx)
      then some (Wire.connect thisPort target)
      else none
  allConnections

/-- Find all active pairs (principal-to-principal connections) -/
def activePairs (g : Graph) : List ActivePair :=
  g.nodes.toList.filterMap fun (id, entry) =>
    match entry.getPrincipal with
    | some target =>
      -- Only include if we're the "smaller" node (deduplication)
      if target.port.isPrincipal && id < target.node.id
      then some (ActivePair.create ⟨id⟩ target.node)
      else none
    | none => none

/-- Check if the graph is in normal form (no active pairs) -/
def isNormalForm (g : Graph) : Bool :=
  g.activePairs.isEmpty

/-- Check if the graph is fully connected (all ports wired) -/
def isFullyConnected (g : Graph) : Bool :=
  g.nodes.toList.all fun (_, entry) => entry.isFullyConnected

/-- Add a definition to the book -/
def addDefinition (g : Graph) (name : QualifiedName) (root : NodeId) (arity : Nat) (ty : Value)
    (isExternal : Bool := false) : Nat × Graph :=
  let idx := g.book.size
  let def_ : Definition := { name, root, arity, ty, isExternal }
  (idx, { g with book := g.book.push def_ })

/-- Look up a definition by index -/
def getDefinition (g : Graph) (idx : Nat) : Option Definition :=
  g.book[idx]?

/-- Update a definition's root node -/
def updateDefinitionRoot (g : Graph) (idx : Nat) (newRoot : NodeId) : Graph :=
  if h : idx < g.book.size then
    let def_ := g.book[idx]
    { g with book := g.book.set idx { def_ with root := newRoot } }
  else g

/-- Look up a definition by name -/
def findDefinition (g : Graph) (name : QualifiedName) : Option (Nat × Definition) :=
  (enumList g.book.toList).find? fun (_, d) => d.name == name

/-- Look up a definition by display name (for backwards compatibility) -/
def findDefinitionByDisplay (g : Graph) (displayName : String) : Option (Nat × Definition) :=
  (enumList g.book.toList).find? fun (_, d) => d.name.display == displayName

/-- Apply a function to all nodes -/
def mapNodes (g : Graph) (f : NodeId → Node → Node) : Graph :=
  let nodes' := g.nodes.toList.foldl (init := g.nodes) fun acc (id, entry) =>
    let newNode := f ⟨id⟩ entry.node
    acc.insert id { entry with node := newNode }
  { g with nodes := nodes' }

/-- Filter nodes by predicate -/
def filterNodes (g : Graph) (p : NodeId → Node → Bool) : List NodeId :=
  g.nodes.toList.filterMap fun (id, entry) =>
    if p ⟨id⟩ entry.node then some ⟨id⟩ else none

/-- Find nodes of a specific type -/
def findNodesByTag (g : Graph) (tag : Tag) : List NodeId :=
  g.filterNodes fun _ n => n.toTag == tag

/-- Collect all DUP labels used in the graph -/
def usedLabels (g : Graph) : List Label :=
  g.nodes.toList.filterMap fun (_, entry) =>
    match entry.node with
    | .dup label => some label
    | _ => none

/-- Extract a subgraph reachable from a port (BFS) -/
partial def reachableFrom (g : Graph) (start : PortId) : List NodeId :=
  let rec go (visited : Std.HashSet Nat) (queue : List PortId) : List NodeId :=
    match queue with
    | [] => visited.toList.map (⟨·⟩)
    | p :: rest =>
      if visited.contains p.node.id then go visited rest
      else
        let visited' := visited.insert p.node.id
        match g.getNode p.node with
        | some entry =>
          let neighbors := entry.connections.filterMap fun (_, target) =>
            if visited'.contains target.node.id then none else some target
          go visited' (rest ++ neighbors.map (·))
        | none => go visited' rest
  go {} [start]

/-- Check if two nodes are connected (path exists) -/
def areConnected (g : Graph) (n1 n2 : NodeId) : Bool :=
  let reachable := g.reachableFrom (PortId.principal n1)
  reachable.any (· == n2)

/-- Collect all node IDs reachable from multiple start ports -/
partial def reachableFromAll (g : Graph) (starts : Array PortId) : Std.HashSet Nat :=
  let rec go (visited : Std.HashSet Nat) (queue : List PortId) : Std.HashSet Nat :=
    match queue with
    | [] => visited
    | p :: rest =>
      if visited.contains p.node.id then go visited rest
      else
        let visited' := visited.insert p.node.id
        match g.getNode p.node with
        | some entry =>
          let neighbors := entry.connections.filterMap fun (_, target) =>
            if visited'.contains target.node.id then none else some target
          go visited' (rest ++ neighbors.map (·))
        | none => go visited' rest
  go {} starts.toList

/-- Remove all nodes not reachable from definition roots and graph root -/
def sweep (g : Graph) : Graph × Nat :=
  let starts := g.book.foldl (init := #[g.root]) fun acc def_ =>
    acc.push (PortId.principal def_.root)
  let live := g.reachableFromAll starts
  let allIds := g.nodes.toList.map (·.1)
  allIds.foldl (init := (g, 0)) fun (g', removed) id =>
    if !live.contains id then
      (g'.removeNode ⟨id⟩, removed + 1)
    else
      (g', removed)

end Graph

/-- State monad for graph construction -/
abbrev GraphM := StateM Graph

namespace GraphM

/-- Run a graph builder starting from an empty graph -/
def run' (m : GraphM α) : α × Graph :=
  Id.run (StateT.run m .empty)

/-- Run and return just the graph -/
def build (m : GraphM α) : Graph :=
  (Id.run (StateT.run m .empty)).2

/-- Allocate a fresh node ID -/
def freshId : GraphM NodeId := do
  let g ← get
  let (nid, g') := g.freshNodeId
  set g'
  return nid

/-- Allocate a fresh label -/
def freshLabel : GraphM Label := do
  let g ← get
  let (label, g') := g.freshLabel
  set g'
  return label

/-- Allocate N labels -/
def freshLabels (n : Nat) : GraphM (Array Label) := do
  let g ← get
  let (labels, g') := g.freshLabels n
  set g'
  return labels

/-- Intern a string, returning its index -/
def internString (s : String) : GraphM Nat := do
  let g ← get
  let (idx, g') := g.internString s
  set g'
  return idx

/-- Add a node to the graph -/
def addNode (n : Node) (ty : Value) : GraphM NodeId := do
  let g ← get
  let (nid, g') := g.addNode n ty
  set g'
  return nid

/-- Set the graph's root port -/
def setRoot (p : PortId) : GraphM Unit := do
  modify fun g => { g with root := p }

/-- Connect two ports -/
def connect (p1 p2 : PortId) : GraphM Unit := do
  modify fun g => g.connect p1 p2

/-- Add a node and connect its principal port to a target -/
def addConnected (n : Node) (target : PortId) (ty : Value) : GraphM NodeId := do
  let nid ← addNode n ty
  connect (PortId.principal nid) target
  return nid

/-- Add a wire between two ports -/
def wire (n1 : NodeId) (p1 : PortIdx) (n2 : NodeId) (p2 : PortIdx) : GraphM Unit := do
  connect ⟨n1, p1⟩ ⟨n2, p2⟩

/-- Convenience: wire principal ports -/
def wirePrincipal (n1 n2 : NodeId) : GraphM Unit := do
  wire n1 .principal n2 .principal

/-- Convenience: wire to auxiliary port -/
def wireToAux (n1 : NodeId) (p1 : PortIdx) (n2 : NodeId) (auxIdx : Nat) : GraphM Unit := do
  wire n1 p1 n2 ⟨auxIdx + 1⟩

/-- Add a definition to the book -/
def addDefinition (name : QualifiedName) (root : NodeId) (arity : Nat) (ty : Value)
    (isExternal : Bool := false) : GraphM Nat := do
  let g ← get
  let (idx, g') := g.addDefinition name root arity ty isExternal
  set g'
  return idx

/-- Get the current graph -/
def getGraph : GraphM Graph := get

/-- Modify the current graph -/
def modifyGraph (f : Graph → Graph) : GraphM Unit := modify f

end GraphM

end Somac.Circuit.Graph
