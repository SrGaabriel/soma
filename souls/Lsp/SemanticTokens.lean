/-
  Semantic Tokens for SouLS
  Provides rich syntax highlighting via LSP semantic tokens protocol
-/
import Lapis.Server.SemanticTokens
import Lsp.State
import Lsp.Cst
import Lsp.Loc

namespace Lsp

open Soma.Syntax
open Lapis.Server.SemanticTokens
open Lapis.Protocol.Generated

/-- Map SymbolKind to LSP SemanticTokenTypes -/
def symbolKindToTokenType : SymbolKind → SemanticTokenTypes
  | .function => .function
  | .type => .type
  | .constructor => .enumMember
  | .field => .property
  | .trait => .interface
  | .method => .method
  | .variable => .variable
  | .typeVariable => .typeParameter
  | .module => .namespace
  | .parameter => .parameter

/-- Map TokenKind to LSP SemanticTokenTypes for non-name tokens -/
def tokenKindToTokenType? : TokenKind → Option SemanticTokenTypes
  | .number => some .number
  | .string _ => some .string
  | .true_ | .false_ => some .keyword
  | .comment => some .comment
  | .varSymbol => some .operator
  | .arrow | .fatArrow | .leftArrow => some .operator
  | .equals | .pipe | .colon | .doubleColon => some .operator
  | .lambda | .forallSymbol | .dollar => some .operator
  | .times | .omega => some .operator
  | k => if k.isKeyword then some .keyword else none

/-- Check if a token is at a definition site by looking at parent nodes -/
def isDefinitionSite (tree : RedTree) (node : RedNode) : Bool :=
  match tree.parent? node with
  | none => false
  | some parent =>
    match parent.syntaxKind? with
    | some .name => true
    | some .operatorName => true
    | some .patVar =>
      -- Pattern variables in function clauses are definitions
      true
    | some .field => true
    | some .constructor => true
    | some .traitMethod => true
    | _ => false

/-- Check if a token is inside an import path (use base/core) -/
partial def isInImportPath (tree : RedTree) (node : RedNode) : Bool :=
  match tree.parent? node with
  | none => false
  | some parent =>
    match parent.syntaxKind? with
    | some .importPath => true
    | some .declUse => true
    | some .sourceFile => false
    | _ => isInImportPath tree parent

/-- Check if node is a descendant of ancestor -/
partial def isDescendantOf (tree : RedTree) (node ancestor : RedNode) : Bool :=
  match tree.parent? node with
  | none => false
  | some parent =>
    parent.id == ancestor.id || isDescendantOf tree parent ancestor

/-- Check if a token is in function position (head of application) -/
partial def isInFunctionPosition (tree : RedTree) (node : RedNode) : Bool :=
  match tree.parent? node with
  | none => false
  | some parent =>
    match parent.syntaxKind? with
    | some .exprApp =>
      -- Check if this node is the first child (the function being applied)
      let children := getChildren tree parent
      if h : 0 < children.size then
        let firstChild := children[0]
        -- The function position could be the node itself or contain it
        firstChild.id == node.id || isDescendantOf tree node firstChild
      else false
    | some .exprVar =>
      -- exprVar wraps the identifier, check if parent of exprVar is exprApp
      isInFunctionPosition tree parent
    | _ => false

/-- Determine the semantic token type for an identifier based on context and symbols -/
def classifyIdentifier (tree : RedTree) (node : RedNode) (symbols : SymbolTable)
    (scopeMap : ScopeMap)
    : Option (SemanticTokenTypes × Array SemanticTokenModifiers) := do
  let text ← node.text?
  let kind ← node.tokenKind?
  let offset := (tree.spanOf node).start.byteOffset

  if let some local_ := scopeMap.resolveByNodeId node.id then
    let tokenType := symbolKindToTokenType local_.kind.toSymbolKind
    return (tokenType, #[.declaration, .definition])

  let isDef := isDefinitionSite tree node
  let modifiers : Array SemanticTokenModifiers :=
    if isDef then #[.declaration, .definition] else #[]

  -- Check if inside import path - these are namespaces
  if isInImportPath tree node then
    return (.namespace, modifiers)

  -- Check if in function position (head of application)
  let isFnPos := isInFunctionPosition tree node

  -- Try local scope resolution
  if let some local_ := scopeMap.resolve text offset then
    let tokenType := symbolKindToTokenType local_.kind.toSymbolKind
    return (tokenType, modifiers)

  -- Then try module-level symbol table
  match symbols.lookupDefinition text with
  | some def_ =>
    let tokenType := symbolKindToTokenType def_.kind
    -- Override to function if in function position and it's a variable
    let tokenType := if isFnPos && tokenType == .variable then .function else tokenType
    return (tokenType, modifiers)
  | none =>
    -- Fallback based on token kind
    match kind with
    | .upperIdent =>
      -- Could be a type or constructor - default to type
      return (.type, modifiers)
    | .lowerIdent =>
      -- Check context to determine if it's a type variable
      let context := deriveContext tree node
      match context with
      | .inTypeSignature | .inTypeExpr =>
        return (.typeParameter, modifiers)
      | _ =>
        -- If in function position, treat as function
        if isFnPos then return (.function, modifiers)
        return (.variable, modifiers)
    | _ => none

/-- Collect a single semantic token from a RedNode -/
def collectTokenFromNode (tree : RedTree) (sf : SourceFile) (node : RedNode)
    (symbols : SymbolTable) (scopeMap : ScopeMap) : Option Token := do
  guard node.isToken
  guard (!node.green.isTrivia)

  let kind ← node.tokenKind?

  -- Skip layout tokens
  guard (!kind.isLayout)

  let span := tree.spanOf node
  let byteLength := span.stop.byteOffset - span.start.byteOffset

  -- Skip zero-length tokens
  guard (byteLength > 0)

  -- Convert to 0-indexed line and UTF-16 character offset
  let line := span.start.line - 1
  let lineContent := getLineContent sf line
  let byteCol := span.start.column - 1
  let character := utf8OffsetToUtf16 lineContent byteCol

  -- Convert byte length to UTF-16 length using the token text
  let text ← node.text?
  let length := utf8LengthToUtf16 text

  -- Classify the token
  if kind.isNameLike then
    let (tokenType, modifiers) ← classifyIdentifier tree node symbols scopeMap
    return Token.ofType line character length tokenType modifiers
  else
    let tokenType ← tokenKindToTokenType? kind
    return Token.ofType line character length tokenType #[]

/-- Collect all semantic tokens from a compiled module -/
def collectSemanticTokens (mod : CompiledModule) : Array Token := Id.run do
  let tree := mod.tree
  let sf := mod.sourceFile
  let symbols := mod.symbols
  let scopeMap := mod.scopeMap
  let mut tokens : Array Token := #[]

  for node in tree.nodes do
    if let some token := collectTokenFromNode tree sf node symbols scopeMap then
      tokens := tokens.push token

  return tokens

/-- Build semantic tokens response for a module -/
def buildSemanticTokens (mod : CompiledModule) : SemanticTokens :=
  let tokens := collectSemanticTokens mod
  let builder := tokens.foldl (fun b t => b.pushToken t) TokenBuilder.new
  builder.build

end Lsp
