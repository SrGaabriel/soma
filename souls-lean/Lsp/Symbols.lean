import Lsp.State
import Lsp.Cst

namespace Lsp

open Soma.Syntax

/-- Extract type signature text from a signature node -/
def extractTypeSignatureText (sigNode : SyntaxNode) : String :=
  -- Get all tokens after ::
  let tokens := sigNode.tokens
  let relevantTokens := tokens.filter fun t =>
    t.kind != .doubleColon && !t.isLayout
  String.intercalate " " (relevantTokens.toList.map (·.text))

/-- Build a DefinitionSite from a CstDefinition -/
def cstDefToDefinitionSite (moduleName filePath : String) (def_ : CstDefinition) : DefinitionSite :=
  let typeStr := def_.signatureNode.map extractTypeSignatureText
  { name := def_.nameToken.text
  , kind := syntaxKindToSymbolKind def_.kind
  , nameSpan := def_.nameToken.span
  , declSpan := def_.declNode.span
  , typeSignature := typeStr
  , moduleName := moduleName
  , filePath := filePath
  }

/-- Extract import info from a use declaration node -/
def extractImportInfo (node : SyntaxNode) : Option ImportInfo := do
  guard (node.kind? == some .declUse)

  let pathNode ← node.findChild? .importPath
  let pathText := pathNode.tokens
    |>.filter (·.kind != .slash)
    |>.toList
    |>.map (·.text)
    |> String.intercalate "/"

  let items := match node.findChild? .importItems with
    | some itemsNode =>
        itemsNode.tokens
          |>.filter (fun t => t.kind == .lowerIdent || t.kind == .upperIdent)
          |>.map (·.text)
    | none => #[]

  some { modulePath := pathText, items, span := node.span }

/-- Build symbol table from CST -/
def buildSymbolTable (moduleName filePath : String) (cst : SyntaxNode) : SymbolTable := Id.run do
  let mut table := SymbolTable.empty

  -- Collect all definitions
  let definitions := collectDefinitions cst
  for def_ in definitions do
    let site := cstDefToDefinitionSite moduleName filePath def_
    table := table.addDefinition site

  -- Collect imports
  let importNodes := cst.collect fun node =>
    node.kind? == some .declUse
  for impNode in importNodes do
    if let some imp := extractImportInfo impNode then
      table := table.addImport imp

  -- Collect references
  let definedNames := table.allNames
  let refs := collectReferences cst definedNames
  for ref in refs do
    table := table.addReference {
      name := ref.token.text
      span := ref.token.span
      context := ref.context
    }

  return table

/-- Format hover content for a definition -/
def formatDefinitionHover (def_ : DefinitionSite) : String :=
  let kindStr := toString def_.kind
  match def_.typeSignature with
  | some sig =>
      s!"```soma\n{def_.name} :: {sig}\n```\n\n*{kindStr}* from `{def_.moduleName}`"
  | none =>
      s!"**{def_.name}**\n\n*{kindStr}* from `{def_.moduleName}`"

/-- Format hover for a keyword -/
def formatKeywordHover (tok : Token) : String :=
  let desc := match tok.kind with
    | .kw_def => "Define a function or value"
    | .kw_let => "Local binding"
    | .kw_in => "Body of let expression"
    | .kw_case => "Pattern matching"
    | .kw_if => "Conditional expression"
    | .kw_then => "Then branch of if"
    | .kw_else => "Else branch of if"
    | .kw_data => "Define an algebraic data type"
    | .kw_struct => "Define a record type"
    | .kw_trait => "Define a type class"
    | .kw_instance => "Define a type class instance"
    | .kw_where => "Begin definition body or constraints"
    | .kw_with => "Add constraints"
    | .kw_use => "Import a module"
    | .kw_export => "Export definitions"
    | .kw_forall => "Universal quantification"
    | .kw_bind => "Monadic bind block"
    | .kw_compose => "Applicative compose block"
    | _ => tok.kind.describe
  s!"**{tok.text}** — {desc}"

/-- Format hover for a syntax construct -/
def formatSyntaxHover (kind : SyntaxKind) (nodeText : String) : String :=
  let preview := if nodeText.length > 50 then nodeText.take 50 ++ "..." else nodeText
  s!"*{kind.describe}*\n```soma\n{preview}\n```"

/-- Get hover information at a position -/
def getHoverAt (offset : Nat) (mod : CompiledModule) (allModules : Array CompiledModule) : Option String := do
  let nodeInfo ← findNodeAtPosition offset mod.cst

  match nodeInfo.node with
  | .token tok =>
      -- Check if it's an identifier
      if tok.kind == .lowerIdent || tok.kind == .upperIdent then
        -- Try to find definition
        if let some def_ := mod.symbols.lookupDefinition tok.text then
          return formatDefinitionHover def_
        -- Try other modules (for imported symbols)
        for other in allModules do
          if let some def_ := other.symbols.lookupDefinition tok.text then
            return formatDefinitionHover def_
        -- Unknown identifier
        return s!"**{tok.text}** — *unknown*"
      else if tok.isKeyword then
        return formatKeywordHover tok
      else
        -- Punctuation or operator
        return s!"`{tok.text}` — {tok.kind.describe}"

  | .node kind _ _ =>
      let text := nodeText nodeInfo.node
      return formatSyntaxHover kind text

  | .error span msg _ =>
      return s!"**Error** at {span.start.line}:{span.start.column}\n\n{msg}"

  | .missing expected loc =>
      return s!"**Missing** at {loc.line}:{loc.column}\n\nExpected: {expected.describe}"

/-- Find definition location for a name -/
def findDefinitionLocation (name : String) (mod : CompiledModule) (allModules : Array CompiledModule)
    : Option (String × Span) := do
  -- Try current module first
  if let some def_ := mod.symbols.lookupDefinition name then
    return (def_.filePath, def_.nameSpan)

  -- Try imported modules based on import declarations
  for imp in mod.symbols.imports do
    -- Find the imported module
    for other in allModules do
      if other.name == imp.modulePath || other.filePath.endsWith imp.modulePath then
        if let some def_ := other.symbols.lookupDefinition name then
          -- Check if it's in the import list (or import list is empty = import all)
          if imp.items.isEmpty || imp.items.contains name then
            return (def_.filePath, def_.nameSpan)

  -- Try all modules as fallback
  for other in allModules do
    if let some def_ := other.symbols.lookupDefinition name then
      return (def_.filePath, def_.nameSpan)

  none

/-- Get definition at a position -/
def getDefinitionAt (offset : Nat) (mod : CompiledModule) (allModules : Array CompiledModule)
    : Option (String × Span) := do
  let nodeInfo ← findNodeAtPosition offset mod.cst

  match nodeInfo.node with
  | .token tok =>
      if tok.kind == .lowerIdent || tok.kind == .upperIdent then
        findDefinitionLocation tok.text mod allModules
      else
        none
  | _ => none

/-- LSP completion item kind numbers -/
def completionKindNumber : SymbolKind → Nat
  | .function => 3      -- Function
  | .type => 22         -- Struct
  | .constructor => 4   -- Constructor
  | .field => 5         -- Field
  | .trait => 8         -- Interface
  | .method => 2        -- Method
  | .variable => 6      -- Variable
  | .typeVariable => 25 -- TypeParameter
  | .module => 9        -- Module
  | .parameter => 6     -- Variable

/-- Get completions based on context -/
def getCompletionsForContext (context : SyntaxContext) (mod : CompiledModule) (allModules : Array CompiledModule)
    : Array DefinitionSite :=
  match context with
  | .inTypeExpr | .inTypeSignature | .afterColon =>
      -- Only type names and type variables
      let localTypes := mod.symbols.definitionsOfKind .type
      let localTyVars := mod.symbols.definitionsOfKind .typeVariable
      let importedTypes := allModules.foldl (fun acc m =>
        acc ++ m.symbols.definitionsOfKind .type) #[]
      localTypes ++ localTyVars ++ importedTypes

  | .inPattern =>
      -- Constructors and variables
      let constructors := mod.symbols.definitionsOfKind .constructor
      let variables := mod.symbols.definitionsOfKind .variable
      let importedCons := allModules.foldl (fun acc m =>
        acc ++ m.symbols.definitionsOfKind .constructor) #[]
      constructors ++ variables ++ importedCons

  | .afterDot _parentExpr =>
      -- TODO: Field completions based on parent type
      mod.symbols.definitionsOfKind .field

  | .inImport | .inImportItems =>
      -- Module names (not implemented yet)
      #[]

  | _ =>
      -- All symbols
      let local_ := mod.symbols.allDefinitions
      let imported := allModules.foldl (fun acc m =>
        acc ++ m.symbols.allDefinitions) #[]
      local_ ++ imported

/-- Get all completions at a position -/
def getCompletionsAt (offset : Nat) (mod : CompiledModule) (allModules : Array CompiledModule)
    : Array DefinitionSite :=
  let context := match findNodeAtPosition offset mod.cst with
    | some nodeInfo => nodeInfo.context
    | none => .unknown
  getCompletionsForContext context mod allModules

/-- Find all references to a name in a module -/
def findReferencesInModule (name : String) (mod : CompiledModule) : Array Span :=
  let refs := mod.symbols.getReferences name
  refs.map (·.span)

/-- Find all references across modules -/
def findAllReferences (name : String) (allModules : Array CompiledModule)
    : Array (String × Span) :=
  allModules.foldl (fun acc mod =>
    let refs := findReferencesInModule name mod
    acc ++ refs.map (mod.filePath, ·)) #[]

/-- LSP symbol kind numbers -/
def documentSymbolKindNumber : SymbolKind → Nat
  | .function => 12     -- Function
  | .type => 5          -- Class
  | .constructor => 9   -- Constructor
  | .field => 8         -- Field
  | .trait => 11        -- Interface
  | .method => 6        -- Method
  | .variable => 13     -- Variable
  | .typeVariable => 26 -- TypeParameter
  | .module => 2        -- Module
  | .parameter => 13    -- Variable

/-- Get document symbols for a module, returns top-level definitions -/
def getDocumentSymbols (mod : CompiledModule) : Array DefinitionSite :=
  mod.symbols.allDefinitions.filter fun def_ =>
    def_.kind == .function ||
    def_.kind == .type ||
    def_.kind == .trait ||
    def_.kind == .constructor

end Lsp
