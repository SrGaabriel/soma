import Soma.Syntax

namespace Lsp

open Soma.Syntax

/-- The syntactic context at a position, derived from CST structure -/
inductive SyntaxContext where
  /-- At module top level -/
  | topLevel
  /-- Inside a declaration (def, data, etc.) -/
  | inDeclaration (kind : SyntaxKind)
  /-- Inside a type signature (after ::) -/
  | inTypeSignature
  /-- Inside a type expression -/
  | inTypeExpr
  /-- Inside an expression -/
  | inExpression
  /-- Inside a pattern -/
  | inPattern
  /-- After a dot (field access context) -/
  | afterDot (parentExpr : SyntaxNode)
  /-- After colon (expecting type) -/
  | afterColon
  /-- In an import path -/
  | inImport
  /-- In an import item list -/
  | inImportItems
  /-- Unknown/other context -/
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
  node : SyntaxNode
  /-- Ancestors from root to parent (not including node itself) -/
  ancestors : Array SyntaxNode
  /-- The derived syntax context -/
  context : SyntaxContext
  deriving Inhabited

namespace NodeAtPosition

/-- Get the parent node (immediate ancestor) -/
def parent? (n : NodeAtPosition) : Option SyntaxNode :=
  if n.ancestors.isEmpty then none
  else some n.ancestors[n.ancestors.size - 1]!

/-- Get the enclosing declaration -/
def enclosingDecl? (n : NodeAtPosition) : Option SyntaxNode :=
  n.ancestors.find? fun node =>
    match node.kind? with
    | some k => k.isDecl
    | none => false

/-- Check if we're inside an error node -/
def hasError (n : NodeAtPosition) : Bool :=
  n.node.isError || n.node.isMissing || n.ancestors.any (·.hasErrors)

end NodeAtPosition

/-- Check if a byte offset is within a span -/
def offsetInSpan (offset : Nat) (span : Span) : Bool :=
  offset >= span.start.byteOffset && offset < span.stop.byteOffset

/-- Check if a byte offset is at the end of a span (for cursor after last char) -/
def offsetAtSpanEnd (offset : Nat) (span : Span) : Bool :=
  offset == span.stop.byteOffset

/--
Find the innermost node containing a byte offset.
Returns the node and the path of ancestors from root.
-/
partial def findNodeAtOffset (offset : Nat) (node : SyntaxNode) (ancestors : Array SyntaxNode := #[])
    : Option (SyntaxNode × Array SyntaxNode) :=
  -- Check if offset is in this node's span
  if !offsetInSpan offset node.span && !offsetAtSpanEnd offset node.span then
    none
  else
    -- Try to find a more specific child
    let newAncestors := ancestors.push node
    let childResult := node.children.findSome? fun child =>
      findNodeAtOffset offset child newAncestors
    match childResult with
    | some result => some result
    | none => some (node, ancestors)

/-- Derive syntax context from a node and its ancestors (helper) -/
def deriveContextFromAncestor (ancestor : SyntaxNode) (node : SyntaxNode) : Option SyntaxContext :=
  match ancestor.kind? with
  | some .signature => some .inTypeSignature
  | some .typeArrow | some .typeApp | some .typeCon | some .typeVar
  | some .typeTuple | some .typeList | some .typeForall | some .typeConstrained
  | some .typeParens | some .typeKinded =>
      some .inTypeExpr
  | some .exprFieldAccess =>
      -- Check if we're after the dot
      let dotChild := ancestor.children.find? (fun c =>
          c.tokenKind? == some .varSymbol || c.tokenText? == some ".")
      match dotChild with
      | some dc =>
          if node.span.start.byteOffset > dc.span.stop.byteOffset then
            some (.afterDot ancestor)
          else
            some .inExpression
      | none => some .inExpression
  | some k =>
      if k.isExpr then some .inExpression
      else if k.isPattern then some .inPattern
      else if k.isDecl then some (.inDeclaration k)
      else none
  | none => none

/-- Derive syntax context from a node and its ancestors -/
def deriveContext (node : SyntaxNode) (ancestors : Array SyntaxNode) : SyntaxContext :=
  -- Check immediate context from ancestors (most recent first)
  let rec checkAncestors (idx : Nat) : Option SyntaxContext :=
    if idx >= ancestors.size then none
    else
      let ancestor := ancestors[ancestors.size - 1 - idx]!
      match deriveContextFromAncestor ancestor node with
      | some ctx => some ctx
      | none => checkAncestors (idx + 1)

  match checkAncestors 0 with
  | some ctx => ctx
  | none =>
      -- Check the node itself
      match node.kind? with
      | some .sourceFile => .topLevel
      | some k =>
          if k.isType then .inTypeExpr
          else if k.isExpr then .inExpression
          else if k.isPattern then .inPattern
          else if k.isDecl then .inDeclaration k
          else .unknown
      | none =>
          -- Token - check ancestors for context
          if ancestors.isEmpty then .topLevel else .unknown

/-- Find node at position with full context information -/
def findNodeAtPosition (offset : Nat) (cst : SyntaxNode) : Option NodeAtPosition := do
  let (node, ancestors) ← findNodeAtOffset offset cst
  let context := deriveContext node ancestors
  some { node, ancestors, context }

/-- Collect all identifier tokens from CST -/
def collectIdentifiers (cst : SyntaxNode) : Array Token :=
  let tokens := cst.tokens
  tokens.filter fun tok =>
    tok.kind == .lowerIdent || tok.kind == .upperIdent

/-- Collect all tokens of a specific kind -/
def collectTokensOfKind (cst : SyntaxNode) (kind : TokenKind) : Array Token :=
  cst.tokens.filter (·.kind == kind)

/-- Information about a definition site in the CST -/
structure CstDefinition where
  /-- The name token -/
  nameToken : Token
  /-- The kind of definition -/
  kind : SyntaxKind
  /-- The full declaration node -/
  declNode : SyntaxNode
  /-- Type signature node (if present) -/
  signatureNode : Option SyntaxNode
  deriving Inhabited

/-- Extract the name token from a declaration node -/
def extractDeclName (node : SyntaxNode) : Option Token :=
  -- Look for .name child first
  match node.findChild? .name with
  | some nameNode => nameNode.firstToken?
  | none =>
      -- Then try .operatorName
      match node.findChild? .operatorName with
      | some opNode =>
          -- Operator name has structure: { op }
          opNode.tokens.find? (·.kind == .varSymbol)
      | none =>
          -- For data/struct, look for upperIdent token directly
          node.tokens.find? (·.kind == .upperIdent)

/-- Extract type signature node from a declaration -/
def extractSignature (node : SyntaxNode) : Option SyntaxNode :=
  node.findChild? .signature

/-- Process a node for definition collection -/
def processNodeForDef (node : SyntaxNode) : Option CstDefinition :=
  match node.kind? with
  | some kind =>
      if kind.isDecl then
        match extractDeclName node with
        | some nameToken => some {
            nameToken
            kind
            declNode := node
            signatureNode := extractSignature node
          }
        | none => none
      else if kind == .constructor then
        -- Data constructors
        match node.tokens.find? (·.kind == .upperIdent) with
        | some tok => some {
            nameToken := tok
            kind := .constructor
            declNode := node
            signatureNode := none
          }
        | none => none
      else if kind == .field then
        -- Struct/constructor fields
        match node.tokens.find? (·.kind == .lowerIdent) with
        | some tok => some {
            nameToken := tok
            kind := .field
            declNode := node
            signatureNode := node.findChild? .typeVar
          }
        | none => none
      else if kind == .traitMethod then
        -- Trait method signatures
        match extractDeclName node with
        | some tok => some {
            nameToken := tok
            kind := .traitMethod
            declNode := node
            signatureNode := extractSignature node
          }
        | none => none
      else if kind == .patVar then
        -- Pattern variables
        match node.firstToken? with
        | some tok => some {
            nameToken := tok
            kind := .patVar
            declNode := node
            signatureNode := none
          }
        | none => none
      else none
  | none => none

/-- Collect all definition sites from CST -/
def collectDefinitions (cst : SyntaxNode) : Array CstDefinition :=
  cst.fold #[] fun acc node =>
    match processNodeForDef node with
    | some def_ => acc.push def_
    | none => acc

/-- A reference to a name in the CST -/
structure CstReference where
  /-- The token referencing the name -/
  token : Token
  /-- Context of the reference -/
  context : SyntaxContext
  deriving Inhabited

/-- Helper to check if a node is a definition site -/
def isDefSiteKind (kind : Option SyntaxKind) : Bool :=
  match kind with
  | some .name | some .patVar => true
  | _ => false

/-- Collect references from a node recursively -/
partial def collectRefsFromNode (node : SyntaxNode) (ancestors : Array SyntaxNode)
    (definedNames : Array String) : Array CstReference :=
  match node with
  | .token tok =>
      if (tok.kind == .lowerIdent || tok.kind == .upperIdent) &&
         definedNames.contains tok.text then
        -- Check if this is a reference (not a definition site)
        let parent := ancestors.back?
        let isDefinition := parent.map (fun p => isDefSiteKind p.kind?) |>.getD false
        if !isDefinition then
          let ctx := deriveContext node ancestors
          #[{ token := tok, context := ctx }]
        else #[]
      else #[]
  | .node _ children _ =>
      let newAncestors := ancestors.push node
      children.foldl (fun acc child =>
        acc ++ collectRefsFromNode child newAncestors definedNames) #[]
  | .error _ _ skipped =>
      let newAncestors := ancestors.push node
      skipped.foldl (fun acc child =>
        acc ++ collectRefsFromNode child newAncestors definedNames) #[]
  | .missing _ _ => #[]

/-- Collect all references to names (excluding definition sites) -/
def collectReferences (cst : SyntaxNode) (definedNames : Array String) : Array CstReference :=
  collectRefsFromNode cst #[] definedNames

/-- Check if a position is in scope of a definition -/
def isInScope (defNode : SyntaxNode) (useOffset : Nat) : Bool :=
  -- todo: make this stronger
  defNode.span.stop.byteOffset <= useOffset

/-- Find all names in scope at a position -/
def namesInScopeAt (offset : Nat) (cst : SyntaxNode) : Array String :=
  let defs := collectDefinitions cst
  defs.filterMap fun def_ =>
    if isInScope def_.declNode offset then
      some def_.nameToken.text
    else
      none

/-- Get the text at a node (joining all tokens) -/
def nodeText (node : SyntaxNode) : String :=
  node.text

/-- Get a display string for a syntax kind -/
def kindDisplayName : SyntaxKind → String
  | .declDef => "function"
  | .declData => "data type"
  | .declStruct => "struct"
  | .declTrait => "trait"
  | .declInstance => "instance"
  | .constructor => "constructor"
  | .field => "field"
  | .traitMethod => "method"
  | .patVar => "variable"
  | .typeVar => "type variable"
  | .typeCon => "type"
  | k => k.describe

/-- Check if a node represents an error -/
def isErrorNode (node : SyntaxNode) : Bool :=
  node.isError || node.isMissing

/-- Get error message if node is an error -/
def errorMessage? (node : SyntaxNode) : Option String :=
  match node with
  | .error _ msg _ => some msg
  | .missing expected _ => some s!"expected {expected}"
  | _ => none

end Lsp
