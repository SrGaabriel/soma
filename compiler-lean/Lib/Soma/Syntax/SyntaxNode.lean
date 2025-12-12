import Soma.Syntax.Source
import Soma.Syntax.Token
import Soma.Syntax.SyntaxKind

namespace Soma.Syntax

/--
A node in the Concrete Syntax Tree.

This is the core representation for parsed source code. It's designed to be
infallible - parsing always produces a tree, with errors represented as
special nodes rather than parse failures.
-/
inductive SyntaxNode where
  /--
  A valid syntax node with a kind and children.
  The span covers from the start of the first child to the end of the last.
  -/
  | node (kind : SyntaxKind) (children : Array SyntaxNode) (span : Span)

  /--
  A token leaf node. Tokens are the leaves of the CST.
  -/
  | token (tok : Token)

  /--
  An error node - the parser encountered invalid syntax but recovered.
  Contains the span of the erroneous region, an error message, and
  any tokens/nodes that were skipped during recovery.
  -/
  | error (span : Span) (message : String) (skipped : Array SyntaxNode)

  /--
  A missing node - expected syntax was not present.
  Contains what kind of syntax was expected and where it was expected.
  -/
  | missing (expected : SyntaxKind) (at_ : SourceLoc)

  deriving Repr, Inhabited

namespace SyntaxNode

/-- Get the span of any syntax node -/
def span : SyntaxNode → Span
  | .node _ _ s => s
  | .token tok => tok.span
  | .error s _ _ => s
  | .missing _ loc => Span.point loc

/-- Get the start location of a node -/
def start (n : SyntaxNode) : SourceLoc := n.span.start

/-- Get the end location of a node -/
def stop (n : SyntaxNode) : SourceLoc := n.span.stop

/-- Check if this is an error node -/
def isError : SyntaxNode → Bool
  | .error .. => true
  | _ => false

/-- Check if this is a missing node -/
def isMissing : SyntaxNode → Bool
  | .missing .. => true
  | _ => false

/-- Check if this node or any descendant has an error -/
partial def hasErrors : SyntaxNode → Bool
  | .error .. => true
  | .missing .. => true
  | .token _ => false
  | .node _ children _ => children.any hasErrors

/-- Get the kind of a node (if it's a .node variant) -/
def kind? : SyntaxNode → Option SyntaxKind
  | .node k _ _ => some k
  | _ => none

/-- Get children of a node (empty for tokens/errors/missing) -/
def children : SyntaxNode → Array SyntaxNode
  | .node _ cs _ => cs
  | .error _ _ skipped => skipped
  | _ => #[]

/-- Get the text content of a token node -/
def tokenText? : SyntaxNode → Option String
  | .token tok => some tok.text
  | _ => none

/-- Get the token kind (if this is a token node) -/
def tokenKind? : SyntaxNode → Option TokenKind
  | .token tok => some tok.kind
  | _ => none

/-- Count all nodes in the tree (for debugging/metrics) -/
partial def nodeCount : SyntaxNode → Nat
  | .node _ children _ => 1 + children.foldl (fun acc c => acc + c.nodeCount) 0
  | .error _ _ skipped => 1 + skipped.foldl (fun acc c => acc + c.nodeCount) 0
  | _ => 1

/-- Count error nodes in the tree -/
partial def errorCount : SyntaxNode → Nat
  | .error _ _ skipped => 1 + skipped.foldl (fun acc c => acc + c.errorCount) 0
  | .missing .. => 1
  | .node _ children _ => children.foldl (fun acc c => acc + c.errorCount) 0
  | .token _ => 0

/-- Find child at index -/
def child? (n : SyntaxNode) (idx : Nat) : Option SyntaxNode :=
  if h : idx < n.children.size then some n.children[idx] else none

/-- Find the first child with the given kind -/
def findChild? (n : SyntaxNode) (kind : SyntaxKind) : Option SyntaxNode :=
  n.children.find? fun c =>
    match c with
    | .node k _ _ => k == kind
    | _ => false

/-- Find all children with the given kind -/
def findChildren (n : SyntaxNode) (kind : SyntaxKind) : Array SyntaxNode :=
  n.children.filter fun c =>
    match c with
    | .node k _ _ => k == kind
    | _ => false

/-- Get the first token in this subtree (for span computation) -/
partial def firstToken? : SyntaxNode → Option Token
  | .token tok => some tok
  | .node _ children _ =>
      children.findSome? firstToken?
  | .error _ _ skipped =>
      skipped.findSome? firstToken?
  | .missing .. => none

/-- Get the last token in this subtree -/
partial def lastToken? : SyntaxNode → Option Token
  | .token tok => some tok
  | .node _ children _ =>
      children.foldr (fun c acc => acc <|> c.lastToken?) none
  | .error _ _ skipped =>
      skipped.foldr (fun c acc => acc <|> c.lastToken?) none
  | .missing .. => none

/-- Get all tokens in this subtree (in order) -/
partial def tokens : SyntaxNode → Array Token
  | .token tok => #[tok]
  | .node _ children _ => children.foldl (fun acc c => acc ++ c.tokens) #[]
  | .error _ _ skipped => skipped.foldl (fun acc c => acc ++ c.tokens) #[]
  | .missing .. => #[]

/-- Get the source text for this node (reconstructed from tokens) -/
def text (n : SyntaxNode) : String :=
  -- Note: This is a simple concatenation. For truly lossless representation,
  -- we'd need to preserve the original source substring.
  String.join (n.tokens.toList.map (·.text))

/-- Filter out trivia (whitespace, comments) from children -/
def nonTriviaChildren (n : SyntaxNode) : Array SyntaxNode :=
  n.children.filter fun c =>
    match c.kind? with
    | some k => !k.isTrivia
    | none =>
      match c with
      | .token tok => !tok.isLayout
      | _ => true

/-- Pretty-print the tree structure (for debugging) -/
partial def debugPrint (n : SyntaxNode) (indent : Nat := 0) : String :=
  let pad := String.ofList (List.replicate indent ' ')
  match n with
  | .node kind children span =>
      let header := s!"{pad}{kind} [{span.start.line}:{span.start.column}]\n"
      let childStrs := children.map (debugPrint · (indent + 2))
      header ++ String.join childStrs.toList
  | .token tok =>
      s!"{pad}TOKEN {tok.kind} \"{tok.text}\"\n"
  | .error span msg _ =>
      s!"{pad}ERROR at [{span.start.line}:{span.start.column}]: {msg}\n"
  | .missing expected loc =>
      s!"{pad}MISSING {expected} at [{loc.line}:{loc.column}]\n"

end SyntaxNode

/-- Create a node, computing span from children. Requires at least one child. -/
def mkNode (kind : SyntaxKind) (children : Array SyntaxNode) (h : children.size > 0 := by decide) : SyntaxNode :=
  let first := children[0]
  let last := children[children.size - 1]
  .node kind children (Span.merge first.span last.span)

/-- Create a node with explicit span (use when children may be empty or span differs from children) -/
def mkNodeSpan (kind : SyntaxKind) (children : Array SyntaxNode) (span : Span) : SyntaxNode :=
  .node kind children span

/-- Create a token node -/
def mkToken (tok : Token) : SyntaxNode :=
  .token tok

/-- Create an error node -/
def mkError (span : Span) (message : String) (skipped : Array SyntaxNode := #[]) : SyntaxNode :=
  .error span message skipped

/-- Create a missing node -/
def mkMissing (expected : SyntaxKind) (at_ : SourceLoc) : SyntaxNode :=
  .missing expected at_

/-! ## Traversal Utilities -/

/-- Fold over all nodes in the tree (pre-order) -/
partial def SyntaxNode.fold (n : SyntaxNode) (init : α) (f : α → SyntaxNode → α) : α :=
  let acc := f init n
  match n with
  | .node _ children _ => children.foldl (fun a c => c.fold a f) acc
  | .error _ _ skipped => skipped.foldl (fun a c => c.fold a f) acc
  | _ => acc

/-- Map a function over all nodes in the tree -/
partial def SyntaxNode.map (n : SyntaxNode) (f : SyntaxNode → SyntaxNode) : SyntaxNode :=
  let mapped := f n
  match mapped with
  | .node kind children span =>
      .node kind (children.map (·.map f)) span
  | .error span msg skipped =>
      .error span msg (skipped.map (·.map f))
  | other => other

/-- Collect all nodes matching a predicate -/
def SyntaxNode.collect (n : SyntaxNode) (pred : SyntaxNode → Bool) : Array SyntaxNode :=
  n.fold #[] fun acc node =>
    if pred node then acc.push node else acc

/-- Collect all error messages in the tree -/
def SyntaxNode.collectErrors (n : SyntaxNode) : Array (Span × String) :=
  n.fold #[] fun acc node =>
    match node with
    | .error span msg _ => acc.push (span, msg)
    | .missing expected loc =>
        acc.push (Span.point loc, s!"expected {expected}")
    | _ => acc

end Soma.Syntax
