import Soma.Syntax

namespace Lsp

open Soma.Syntax

/-- The syntactic context at a position, derived from CST structure -/
inductive SyntaxContext where
  | topLevel
  | inDeclaration (kind : SyntaxKind)
  | inTypeSignature
  | inTypeExpr
  | inExpression
  | inPattern
  | afterDot (parentId : NodeId)
  | afterColon
  | inImport
  | inImportItems
  | unknown
  deriving Inhabited, Repr

instance : ToString SyntaxContext where
  toString
    | .topLevel => "top-level"
    | .inDeclaration k => s!"in {k}"
    | .inTypeSignature => "in type signature"
    | .inTypeExpr => "in type expression"
    | .inExpression => "in expression"
    | .inPattern => "in pattern"
    | .afterDot _ => "after dot"
    | .afterColon => "after colon"
    | .inImport => "in import"
    | .inImportItems => "in import items"
    | .unknown => "unknown"

/-- Result of finding a node at a position -/
structure NodeAtPosition where
  /-- The innermost node at the position -/
  node : RedNode
  /-- The red tree (for parent lookups) -/
  tree : RedTree
  /-- The derived syntax context -/
  context : SyntaxContext
  deriving Inhabited

namespace NodeAtPosition

/-- Get the parent node - O(1) via parentIdx -/
def parent? (n : NodeAtPosition) : Option RedNode :=
  n.tree.parent? n.node

/-- Get ancestors from node to root -/
partial def ancestors (n : NodeAtPosition) : Array RedNode :=
  go #[] (n.tree.parent? n.node)
where
  go (acc : Array RedNode) : Option RedNode → Array RedNode
    | none => acc
    | some node => go (acc.push node) (n.tree.parent? node)

/-- Get the enclosing declaration -/
partial def enclosingDecl? (n : NodeAtPosition) : Option RedNode :=
  go (some n.node)
where
  go : Option RedNode → Option RedNode
    | none => none
    | some node =>
        match node.syntaxKind? with
        | some k => if k.isDecl then some node else go (n.tree.parent? node)
        | none => go (n.tree.parent? node)

/-- Check if we're inside an error node -/
partial def hasError (n : NodeAtPosition) : Bool :=
  go (some n.node)
where
  go : Option RedNode → Bool
    | none => false
    | some node => node.isError || go (n.tree.parent? node)

/-- Get the span of the node -/
def span (n : NodeAtPosition) : Span :=
  n.tree.spanOf n.node

end NodeAtPosition

/-- Derive syntax context by walking up from a node -/
partial def deriveContext (tree : RedTree) (node : RedNode) : SyntaxContext :=
  go (some node)
where
  go : Option RedNode → SyntaxContext
    | none => .unknown
    | some n =>
        match n.syntaxKind? with
        | some kind =>
            match kind with
            | .signature => .inTypeSignature
            | .typeArrow | .typeApp | .typeCon | .typeVar
            | .typeTuple | .typeList | .typeForall | .typeConstrained
            | .typeParens | .typeKinded => .inTypeExpr
            | .exprFieldAccess =>
                -- Check if we're after the dot by comparing offsets
                if node.offset > n.offset then .afterDot n.id
                else .inExpression
            | .declUse => .inImport
            | .importItems => .inImportItems
            | .sourceFile => .topLevel
            | k =>
                if k.isExpr then .inExpression
                else if k.isPattern then .inPattern
                else if k.isDecl then .inDeclaration k
                else go (tree.parent? n)
        | none => go (tree.parent? n)

/-- Find node at position with full context -/
def findNodeAtPosition (offset : Nat) (tree : RedTree) : Option NodeAtPosition := do
  let node ← tree.nodeAtOffset? offset
  let context := deriveContext tree node
  some { node, tree, context }

/-- Information about a definition site -/
structure CstDefinition where
  /-- The name (text) -/
  name : String
  /-- The kind of definition -/
  kind : SyntaxKind
  /-- NodeId of the declaration (stable across reparses) -/
  declId : NodeId
  /-- NodeId of the name token -/
  nameId : NodeId
  /-- Span of the name -/
  nameSpan : Span
  /-- Span of the full declaration -/
  declSpan : Span
  /-- Type signature text (if present) -/
  typeSignature : Option String
  deriving Inhabited, Repr

/-- Get children of a RedNode as RedNodes (not GreenNodes) -/
def getChildren (tree : RedTree) (node : RedNode) : Array RedNode := Id.run do
  let mut children := #[]
  let mut idx := node.selfIdx + 1
  for child in node.green.children do
    if h : idx < tree.nodes.size then
      children := children.push tree.nodes[idx]
      idx := idx + RedTree.countGreenNodes child
  return children

/-- Find a child with a specific SyntaxKind -/
def findChild? (tree : RedTree) (node : RedNode) (kind : SyntaxKind) : Option RedNode :=
  (getChildren tree node).find? fun c => c.syntaxKind? == some kind

/-- Get all tokens under a node -/
def getTokens (tree : RedTree) (node : RedNode) : Array RedNode :=
  let startIdx := node.selfIdx
  let endIdx := startIdx + RedTree.countGreenNodes node.green
  tree.nodes[startIdx:endIdx].toArray.filter fun n =>
    n.isToken && !n.green.isTrivia

/-- Find the first token of a specific kind under a node -/
def findToken? (tree : RedTree) (node : RedNode) (kind : TokenKind) : Option RedNode :=
  (getTokens tree node).find? fun t => t.tokenKind? == some kind

/-- Get first token under a node -/
def firstToken? (tree : RedTree) (node : RedNode) : Option RedNode :=
  (getTokens tree node).toList.head?

/-- Get text of all tokens under a node, joined -/
def nodeText (tree : RedTree) (node : RedNode) : String :=
  let tokens := getTokens tree node
  String.join (tokens.toList.filterMap (·.text?))

/-- Extract signature text from a signature node -/
def extractSignatureText (tree : RedTree) (sigNode : RedNode) : String :=
  let tokens := getTokens tree sigNode
  let relevantTokens := tokens.filter fun t =>
    t.tokenKind? != some .doubleColon && !t.green.isTrivia
  String.intercalate " " (relevantTokens.toList.filterMap (·.text?))

/-- Extract a definition from a declaration node -/
def extractDefinition (tree : RedTree) (node : RedNode) : Option CstDefinition := do
  let kind ← node.syntaxKind?
  guard (kind.isDecl || kind == .constructor || kind == .field || kind == .traitMethod || kind == .patVar || kind == .composeLetStmt)

  -- Find the name token
  let nameToken ←
    if kind == .constructor then
      findToken? tree node .upperIdent
    else if kind == .field || kind == .patVar then
      findToken? tree node .lowerIdent
    else if kind == .composeLetStmt then
      -- composeLetStmt structure: [letTok, nameTok/pattern, eqTok, value]
      -- The name is the first lowerIdent token (if it's a simple binding)
      let children := getChildren tree node
      -- Skip the 'let' keyword, look for lowerIdent in second child
      if h : 1 < children.size then
        let second := children[1]
        if second.tokenKind? == some .lowerIdent then
          some second
        else
          -- It's a pattern, try to find a patVar inside
          findToken? tree second .lowerIdent
      else
        none
    else
      -- Look for .name child first, then .operatorName, then direct token
      match findChild? tree node .name with
      | some nameNode => firstToken? tree nameNode
      | none =>
          match findChild? tree node .operatorName with
          | some opNode => findToken? tree opNode .varSymbol
          | none => findToken? tree node .upperIdent <|> findToken? tree node .lowerIdent

  let name ← nameToken.text?
  let sigNode? := findChild? tree node .signature
  let typeSignature := sigNode?.map (extractSignatureText tree ·)

  some {
    name
    kind
    declId := node.id
    nameId := nameToken.id
    nameSpan := tree.spanOf nameToken
    declSpan := tree.spanOf node
    typeSignature
  }

/-- Collect all definitions from a RedTree -/
def collectDefinitions (tree : RedTree) : Array CstDefinition :=
  tree.nodes.filterMap (extractDefinition tree ·)

/-- A reference to a name -/
structure CstReference where
  /-- The referenced name -/
  name : String
  /-- NodeId of the reference token -/
  tokenId : NodeId
  /-- Span of the reference -/
  span : Span
  /-- Context of the reference -/
  context : SyntaxContext
  deriving Inhabited, Repr

/-- Check if a node is a definition site (name node in a declaration) -/
def isDefSite (tree : RedTree) (node : RedNode) : Bool :=
  match tree.parent? node with
  | some parent =>
      match parent.syntaxKind? with
      | some .name | some .patVar | some .operatorName => true
      | _ => false
  | none => false

/-- Collect all references to known names -/
def collectReferences (tree : RedTree) (definedNames : Array String) : Array CstReference :=
  tree.nodes.filterMap fun node => do
    -- Only identifier tokens (todo: review)
    guard (node.tokenKind? == some .lowerIdent || node.tokenKind? == some .upperIdent)
    let name ← node.text?
    guard (definedNames.contains name)
    guard (!isDefSite tree node)
    let context := deriveContext tree node
    some { name, tokenId := node.id, span := tree.spanOf node, context }

/-- Find all names in scope at a position -/
def namesInScopeAt (offset : Nat) (tree : RedTree) : Array String :=
  let defs := collectDefinitions tree
  defs.filterMap fun def_ =>
    if def_.declSpan.stop.byteOffset <= offset then
      some def_.name
    else
      none

/-- Get a display string for a syntax kind -/
def kindDisplayName : SyntaxKind → String
  | .declDef => "function"
  | .declInductive => "inductive type"
  | .declStruct => "struct"
  | .declTrait => "class"
  | .declInstance => "instance"
  | .constructor => "constructor"
  | .field => "field"
  | .traitMethod => "method"
  | .patVar => "variable"
  | .composeLetStmt => "local binding"
  | .typeVar => "type variable"
  | .typeCon => "type"
  | k => k.describe

/-- Check if a node represents an error -/
def isErrorNode (node : RedNode) : Bool :=
  node.isError

/-- Get error message if node is an error -/
def errorMessage? (node : RedNode) : Option String :=
  match node.green with
  | .error msg _ _ => some msg
  | .missing expected => some s!"expected {expected}"
  | _ => none

end Lsp
