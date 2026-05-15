import Soma.Syntax.GreenTree
import Soma.Syntax.Source

namespace Soma.Syntax

structure NodeId where
  id : UInt64
  deriving BEq, Hashable, Repr, Inhabited

instance : ToString NodeId where
  toString n := s!"NodeId({n.id})"

/-- Counter for generating fresh NodeIds -/
structure NodeIdGen where
  next : UInt64 := 1
  deriving Inhabited

namespace NodeIdGen

def fresh (gen : NodeIdGen) : NodeIdGen × NodeId :=
  ({ next := gen.next + 1 }, ⟨gen.next⟩)

end NodeIdGen

/-- A red node: a green node with position and identity -/
structure RedNode where
  /-- The underlying green node -/
  green : GreenNode
  /-- Stable identifier for this node -/
  id : NodeId
  /-- Absolute byte offset in source -/
  offset : Nat
  /-- Index of parent in the tree (none for root) -/
  parentIdx : Option Nat
  /-- Index of this node in the flattened tree -/
  selfIdx : Nat
  deriving Repr, Inhabited

namespace RedNode

end RedNode

/-- A complete red tree -/
structure RedTree where
  /-- All nodes in pre-order -/
  nodes : Array RedNode
  /-- The source file -/
  source : SourceFile
  /-- Mapping from NodeId to index for O(1) lookup -/
  idToIdx : Std.HashMap NodeId Nat
  deriving Inhabited

namespace RedTree

/-- Count nodes in a green subtree -/
partial def countGreenNodes (g : GreenNode) : Nat :=
  1 + g.children.foldl (fun acc c => acc + countGreenNodes c) 0

end RedTree

-- todo: review if this approach isn't too OOP-like
/-- State for building a red tree -/
structure RedTreeBuilder where
  /-- Accumulated nodes -/
  nodes : Array RedNode := #[]
  /-- NodeId generator -/
  idGen : NodeIdGen := {}
  /-- ID to index mapping -/
  idToIdx : Std.HashMap NodeId Nat := {}
  deriving Inhabited

namespace RedTreeBuilder

/-- Add a node and return its index -/
def addNode (b : RedTreeBuilder) (green : GreenNode) (id : NodeId)
    (offset : Nat) (parentIdx : Option Nat) : RedTreeBuilder × Nat :=
  let idx := b.nodes.size
  let node : RedNode := { green, id, offset, parentIdx, selfIdx := idx }
  let b := { b with
    nodes := b.nodes.push node
    idToIdx := b.idToIdx.insert id idx
  }
  (b, idx)

/-- Generate a fresh NodeId -/
def freshId (b : RedTreeBuilder) : RedTreeBuilder × NodeId :=
  let (gen, id) := b.idGen.fresh
  ({ b with idGen := gen }, id)

end RedTreeBuilder

/-- Build a red tree from a green tree, assigning fresh NodeIds -/
partial def buildRedTree (green : GreenNode) (source : SourceFile) : RedTree :=
  let builder := go {} green 0 none
  { nodes := builder.nodes
  , source := source
  , idToIdx := builder.idToIdx
  }
where
  go (b : RedTreeBuilder) (g : GreenNode) (offset : Nat) (parentIdx : Option Nat) : RedTreeBuilder := Id.run do
    let (b, id) := b.freshId
    let (b, myIdx) := b.addNode g id offset parentIdx
    -- Add children
    let mut b := b
    let mut childOffset := offset
    for child in g.children do
      b := go b child childOffset (some myIdx)
      childOffset := childOffset + child.width
    return b

/-- Result of diffing two green nodes -/
inductive DiffResult where
  /-- Nodes are identical (same hash), reuse old NodeId -/
  | same (oldId : NodeId)
  /-- Nodes differ, need new NodeId -/
  | different
  deriving Repr



/-- Parse result containing both trees -/
structure ParsedTree where
  /-- The immutable green tree -/
  green : GreenNode
  /-- The positioned red tree with stable NodeIds -/
  red : RedTree
  deriving Inhabited

/-- Create a parsed tree from a green tree (initial parse) -/
def ParsedTree.fromGreen (green : GreenNode) (source : SourceFile) : ParsedTree :=
  { green, red := buildRedTree green source }

end Soma.Syntax
