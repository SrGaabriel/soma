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
open Soma.Dependent (Globals GlobalInfo)
open Lapis.Server.SemanticTokens
open Lapis.Protocol.Generated

/-- Map SymbolKind to LSP SemanticTokenTypes -/
def symbolKindToTokenType : SymbolKind → SemanticTokenTypes
  | .function => .function
  | .theorem_ => .function
  | .type => .type
  | .typeAlias => .type
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
  | .leftParen | .rightParen | .leftBrace | .rightBrace
  | .leftBracket | .rightBracket | .leftAngle | .rightAngle
  | .comma | .dot | .at => some .operator
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

/-- Check if a token is inside an import path (the `base::op` part of a `use`) -/
partial def isInImportPath (tree : RedTree) (node : RedNode) : Bool :=
  match tree.parent? node with
  | none => false
  | some parent =>
    match parent.syntaxKind? with
    | some .importPath => true
    | some .importItems => false
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

/-- Walk up through `.triviaToken` wrappers to find the semantic parent node -/
private partial def semanticParent? (tree : RedTree) (node : RedNode) : Option RedNode :=
  match tree.parent? node with
  | none => none
  | some p =>
    if p.syntaxKind? == some .triviaToken then semanticParent? tree p
    else some p

/-- Identifier tokens under `parent`, in source order -/
private def collectPathIdents (tree : RedTree) (parent : RedNode) : Array RedNode :=
  (getTokens tree parent).filter fun t =>
    t.tokenKind? == some .lowerIdent || t.tokenKind? == some .upperIdent

/-- Kinds that wrap a `::`-separated qualified name -/
private def isQualifiedPathWrapper : SyntaxKind → Bool
  | .exprVar | .typeCon | .name => true
  | _ => false

/-- Map a `GlobalInfo` to an LSP `SymbolKind` so imported symbols classify correctly -/
private def globalInfoToSymbolKind (info : GlobalInfo) : SymbolKind :=
  if info.isConstructor then .constructor
  else match info.origin with
    | .typeDecl => .type
    | .class_ => .trait
    | .constructor => .constructor
    | .projection => .field
    | .traitMethod => .method
    | .theorem_ => .theorem_
    | .intrinsic | .extern => .function
    | _ => .function

/-- Resolve the prefix of a qualified path up to and including `node` in globals -/
private def classifyPathSegment (tree : RedTree) (parent node : RedNode)
    (globals : Option Globals) (moduleName : String) : SemanticTokenTypes := Id.run do
  let idents := collectPathIdents tree parent
  let idx := (idents.findIdx? (·.id == node.id)).getD 0
  let segs := (idents.extract 0 (idx + 1)).filterMap (·.text?)
  if segs.size == 0 then return .namespace
  let some g := globals | return .namespace
  let name := segs[segs.size - 1]!
  let path := segs.extract 0 (segs.size - 1)
  let currentNs := moduleName.splitOn "::" |>.toArray
  match (g.resolve currentNs path name).bind g.getDef with
  | none => return .namespace
  | some info => return symbolKindToTokenType (globalInfoToSymbolKind info)

/-- Classify an identifier based on the CST kind of its enclosing node -/
def classifyByContext (tree : RedTree) (node : RedNode) (kind : TokenKind)
    : Option SemanticTokenTypes := Id.run do
  let some parent := semanticParent? tree node | return none
  match parent.syntaxKind? with
  | some .exprFieldAccess =>
    if kind == .lowerIdent then return some .property
  | some .exprProjection =>
    -- Structure: [Type, dot, field]
    if kind == .upperIdent then return some .type
    if kind == .lowerIdent then return some .property
  | some .recordField =>
    if kind == .lowerIdent then return some .property
  | some .exprVariant | some .patVariant =>
    return some .enumMember
  | some .attribute =>
    if kind == .lowerIdent then return some .decorator
  | some .name =>
    let idents := collectPathIdents tree parent
    if idents.size == 1 then
      match tree.parent? parent with
      | some gp =>
        if gp.syntaxKind? == some .patCon && kind == .upperIdent then
          return some .enumMember
      | none => pure ()
  | _ => pure ()
  return none

/-- Determine the semantic token type for an identifier based on context and symbols -/
def classifyIdentifier (tree : RedTree) (node : RedNode) (symbols : SymbolTable)
    (scopeMap : ScopeMap) (globals : Option Globals) (moduleName : String)
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

  if let some ctxType := classifyByContext tree node kind then
    return (ctxType, modifiers)

  if let some parent := semanticParent? tree node then
    if let some pk := parent.syntaxKind? then
      if isQualifiedPathWrapper pk then
        let idents := collectPathIdents tree parent
        if idents.size > 1 then
          return (classifyPathSegment tree parent node globals moduleName, modifiers)

  -- Check if in function position (head of application)
  let isFnPos := isInFunctionPosition tree node

  -- Try local scope resolution
  if let some local_ := scopeMap.resolve text offset then
    let tokenType := symbolKindToTokenType local_.kind.toSymbolKind
    return (tokenType, modifiers)

  -- Then try module-level symbol table
  if let some def_ := symbols.lookupDefinition text then
    let tokenType := symbolKindToTokenType def_.kind
    let tokenType := if isFnPos && tokenType == .variable then .function else tokenType
    let mods := if def_.kind == .theorem_ then modifiers.push .readonly else modifiers
    return (tokenType, mods)

  if let some g := globals then
    let currentNs := moduleName.splitOn "::" |>.toArray
    if let some qn := g.resolve currentNs #[] text then
      if let some info := g.getDef qn then
        let symKind := globalInfoToSymbolKind info
        let tokenType := symbolKindToTokenType symKind
        let tokenType := if isFnPos && tokenType == .variable then .function else tokenType
        let mods := if symKind == .theorem_ then modifiers.push .readonly else modifiers
        return (tokenType, mods)

  match kind with
  | .upperIdent =>
    return (.type, modifiers)
  | .lowerIdent =>
    let context := deriveContext tree node
    match context with
    | .inTypeSignature | .inTypeExpr =>
      return (.typeParameter, modifiers)
    | _ =>
      if isFnPos then return (.function, modifiers)
      return (.variable, modifiers)
  | _ => none

/-- Collect a single semantic token from a RedNode -/
def collectTokenFromNode (tree : RedTree) (sf : SourceFile) (node : RedNode)
    (symbols : SymbolTable) (scopeMap : ScopeMap) (globals : Option Globals)
    (moduleName : String) : Option Token := do
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

  match semanticParent? tree node with
  | some p =>
    if p.syntaxKind? == some .attribute then
      return Token.ofType line character length .decorator #[]
  | none => pure ()

  -- Classify the token
  if kind.isNameLike then
    let (tokenType, modifiers) ←
      classifyIdentifier tree node symbols scopeMap globals moduleName
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
  let globals := mod.globals
  let moduleName := mod.name
  let mut tokens : Array Token := #[]

  for node in tree.nodes do
    if let some token := collectTokenFromNode tree sf node symbols scopeMap globals moduleName then
      tokens := tokens.push token

  return tokens

/-- Build semantic tokens response for a module -/
def buildSemanticTokens (mod : CompiledModule) : SemanticTokens :=
  let tokens := collectSemanticTokens mod
  let builder := tokens.foldl (fun b t => b.pushToken t) TokenBuilder.new
  builder.build

end Lsp
