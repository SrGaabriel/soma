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

/-- Get the width of this node -/
def width (n : RedNode) : Nat := n.green.width

/-- Get the end offset of this node -/
def endOffset (n : RedNode) : Nat := n.offset + n.width

/-- Check if this is a token -/
def isToken (n : RedNode) : Bool := n.green.isToken

/-- Check if this is an error -/
def isError (n : RedNode) : Bool := n.green.isError

/-- Get the token kind if this is a token -/
def tokenKind? (n : RedNode) : Option TokenKind := n.green.tokenKind?

/-- Get the syntax kind if this is an interior node -/
def syntaxKind? (n : RedNode) : Option SyntaxKind := n.green.syntaxKind?

/-- Get the text if this is a token -/
def text? (n : RedNode) : Option String := n.green.text?

/-- Get the raw kind -/
def rawKind (n : RedNode) : RawKind := n.green.rawKind

/-- Compute the span of this node given a source file -/
def span (n : RedNode) (source : SourceFile) : Span :=
  Span.fromOffsets source n.offset n.endOffset

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

/-- Get the root node -/
def root (t : RedTree) : Option RedNode :=
  if h : 0 < t.nodes.size then some t.nodes[0] else none

/-- Get a node by index -/
def get? (t : RedTree) (idx : Nat) : Option RedNode :=
  if h : idx < t.nodes.size then some t.nodes[idx] else none

/-- Get a node by NodeId -/
def getById? (t : RedTree) (id : NodeId) : Option RedNode := do
  let idx ← t.idToIdx.get? id
  t.get? idx

/-- Get the parent of a node -/
def parent? (t : RedTree) (n : RedNode) : Option RedNode := do
  let parentIdx ← n.parentIdx
  t.get? parentIdx

/-- Get the span of a node -/
def spanOf (t : RedTree) (n : RedNode) : Span :=
  n.span t.source

/-- Get the span of a node by id -/
def spanOfId? (t : RedTree) (id : NodeId) : Option Span := do
  let node ← t.getById? id
  some (t.spanOf node)

/-- Count nodes in a green subtree -/
partial def countGreenNodes (g : GreenNode) : Nat :=
  1 + g.children.foldl (fun acc c => acc + countGreenNodes c) 0

/-- Find the node at a byte offset (innermost containing node) -/
partial def nodeAtOffset? (t : RedTree) (offset : Nat) : Option RedNode := do
  -- Start from root and descend
  let root ← t.root
  if offset < root.offset || offset >= root.endOffset then
    return root  -- Return root even if offset is outside (for edge cases)
  findInnermost root
where
  findInnermost (node : RedNode) : Option RedNode := Id.run do
    -- Check children
    let mut currentIdx := node.selfIdx + 1
    let mut childOffset := node.offset
    for child in node.green.children do
      if h : currentIdx < t.nodes.size then
        let childNode := t.nodes[currentIdx]
        if offset >= childOffset && offset < childOffset + child.width then
          -- Offset is within this child, recurse
          return findInnermost childNode
        childOffset := childOffset + child.width
        currentIdx := currentIdx + countGreenNodes child
    -- No child contains the offset, return this node
    return some node

/-- Collect all nodes matching a predicate -/
def collect (t : RedTree) (pred : RedNode → Bool) : Array RedNode :=
  t.nodes.filter pred

/-- Get all tokens in order -/
def tokens (t : RedTree) : Array RedNode :=
  t.nodes.filter (·.isToken)

/-- Find a node by NodeId -/
def findById (t : RedTree) (id : NodeId) : Option Nat :=
  t.idToIdx.get? id

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

/-- Diff a new green node against an old red node -/
def diffNode (oldNode : RedNode) (newGreen : GreenNode) : DiffResult :=
  if oldNode.green.contentHash == newGreen.contentHash then
    .same oldNode.id
  else
    .different

/-- Get the child RedNodes of a node in the tree -/
partial def getOldChildren (tree : RedTree) (node : RedNode) : Array RedNode := Id.run do
  let mut children := #[]
  let mut idx := node.selfIdx + 1
  for _ in node.green.children do
    if h : idx < tree.nodes.size then
      children := children.push tree.nodes[idx]
      idx := idx + RedTree.countGreenNodes tree.nodes[idx].green
  return children

/-- Build a red tree from a new green tree, reusing NodeIds from an old tree
where the content is unchanged.

todo: handle insertions/deletions better
-/
partial def diffRedTree (oldTree : RedTree) (newGreen : GreenNode) (source : SourceFile)
    (startGen : NodeIdGen := {}) : RedTree :=
  let builder := go { idGen := startGen } newGreen 0 none (oldTree.root)
  { nodes := builder.nodes
  , source := source
  , idToIdx := builder.idToIdx
  }
where
  go (b : RedTreeBuilder) (g : GreenNode) (offset : Nat) (parentIdx : Option Nat)
      (oldNode? : Option RedNode) : RedTreeBuilder := Id.run do
    -- Check if we can reuse the old NodeId
    let (b, id) := match oldNode? with
      | some oldNode =>
        match diffNode oldNode g with
        | .same oldId => (b, oldId)
        | .different => b.freshId
      | none => b.freshId

    let (b, myIdx) := b.addNode g id offset parentIdx

    -- Process children, trying to match with old children
    let mut b := b
    let mut childOffset := offset
    let oldChildren := oldNode?.map (fun n => getOldChildren oldTree n) |>.getD #[]

    for h : i in [:g.children.size] do
      let child := g.children[i]
      let oldChild := if h2 : i < oldChildren.size then some oldChildren[i] else none
      b := go b child childOffset (some myIdx) oldChild
      childOffset := childOffset + child.width
    return b

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

/-- Compute the max NodeId used in a tree -/
def maxNodeId (tree : RedTree) : UInt64 :=
  tree.nodes.foldl (fun acc n => max acc n.id.id) 0

/-- Reparse with a new green tree, preserving NodeIds where possible -/
def ParsedTree.reparse (old : ParsedTree) (newGreen : GreenNode) (source : SourceFile) : ParsedTree :=
  let startGen : NodeIdGen := { next := maxNodeId old.red + 1 }
  { green := newGreen
  , red := diffRedTree old.red newGreen source startGen
  }

end Soma.Syntax
