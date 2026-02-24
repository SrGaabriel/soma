import Std.Data.HashSet
import Lsp.State
import Lsp.Cst
import Soma.Core.Quote
import Soma.Dependent.Monad

namespace Lsp

open Std

open Soma.Syntax
open Soma.Project (Symbol SymbolEnv SymbolKind)
open Soma.Core (Value valueToString)
open Soma.Dependent (Globals GlobalInfo)

/-- Build a DefinitionSite from a CstDefinition -/
def cstDefToDefinitionSite (moduleName filePath : String) (def_ : CstDefinition) : DefinitionSite :=
  { name := def_.name
  , kind := syntaxKindToSymbolKind def_.kind
  , nameSpan := def_.nameSpan
  , declSpan := def_.declSpan
  , typeSignature := def_.typeSignature
  , moduleName := moduleName
  , filePath := filePath
  }

/-- Extract import info from a use declaration node -/
def extractImportInfo (tree : RedTree) (node : RedNode) : Option ImportInfo := do
  guard (node.syntaxKind? == some .declUse)

  let pathNode ← findChild? tree node .importPath
  let pathTokens := getTokens tree pathNode
  let pathText := pathTokens
    |>.filter (·.tokenKind? != some .slash)
    |>.toList
    |>.filterMap (·.text?)
    |> String.intercalate "/"

  let items := match findChild? tree node .importItems with
    | some itemsNode =>
        let tokens := getTokens tree itemsNode
        tokens
          |>.filter (fun t => t.tokenKind? == some .lowerIdent || t.tokenKind? == some .upperIdent)
          |>.filterMap (·.text?)
    | none => #[]

  some { modulePath := pathText, items, span := tree.spanOf node }

/-- Build symbol table from RedTree (full rebuild) -/
def buildSymbolTable (moduleName filePath : String) (tree : RedTree) : SymbolTable := Id.run do
  let mut table := SymbolTable.empty

  -- Collect all definitions
  let definitions := collectDefinitions tree
  for def_ in definitions do
    let site := cstDefToDefinitionSite moduleName filePath def_
    table := table.addDefinition site

  -- Collect imports
  let importNodes := tree.nodes.filter fun node =>
    node.syntaxKind? == some .declUse
  for impNode in importNodes do
    if let some imp := extractImportInfo tree impNode then
      table := table.addImport imp

  -- Collect references
  let definedNames := table.allNames
  let refs := collectReferences tree definedNames
  for ref in refs do
    table := table.addReference {
      name := ref.name
      span := ref.span
      context := ref.context
    }

  return table

/-- Update symbol table incrementally for changed declarations -/
def updateSymbolTableIncremental
    (oldSymbols : SymbolTable)
    (tree : RedTree)
    (changedDeclIds : HashSet NodeId)
    (moduleName filePath : String) : SymbolTable := Id.run do
  -- Start with old symbols
  let mut definitions := oldSymbols.definitions
  let mut references := oldSymbols.references

  -- Collect all new definitions
  let allDefs := collectDefinitions tree

  -- Find names of changed declarations (to remove old entries)
  let changedNames : HashSet String := allDefs.foldl (fun acc def_ =>
    if changedDeclIds.contains def_.declId then acc.insert def_.name
    else acc) {}

  -- Remove old definitions for changed declarations
  for name in changedNames do
    definitions := definitions.erase name
    references := references.erase name

  -- Add new definitions for changed declarations
  for def_ in allDefs do
    if changedDeclIds.contains def_.declId then
      let site := cstDefToDefinitionSite moduleName filePath def_
      definitions := definitions.insert def_.name site

  -- Rebuild references for changed declarations
  let definedNames := definitions.toArray.map (·.1)
  let allRefs := collectReferences tree definedNames

  -- Clear and rebuild references that involve changed names
  for name in changedNames do
    references := references.erase name

  -- Add all references (simpler than trying to be incremental here)
  let mut newRefs : Std.HashMap String (Array SymbolReference) := references
  for ref in allRefs do
    let existing := newRefs.getD ref.name #[]
    -- Avoid duplicates by checking span
    let isDuplicate := existing.any (·.span == ref.span)
    if !isDuplicate then
      newRefs := newRefs.insert ref.name (existing.push {
        name := ref.name
        span := ref.span
        context := ref.context
      })

  -- Imports don't change incrementally (they're top-level)
  let imports := tree.nodes.filterMap fun node =>
    if node.syntaxKind? == some .declUse then
      extractImportInfo tree node
    else none

  return {
    definitions := definitions
    references := newRefs
    imports := imports
  }

/-- Format hover content for a definition -/
def formatDefinitionHover (def_ : DefinitionSite) (globals : Option Globals := none) : String :=
  let kindStr := toString def_.kind
  -- First try CST signature, then fall back to inferred type from globals
  let typeStr : Option String :=
    match def_.typeSignature with
    | some sig => some sig
    | none =>
        -- Try to get inferred type from globals
        globals.bind fun g => g.lookup def_.name |>.map fun info => valueToString info.type
  match typeStr with
  | some sig =>
      s!"```soma\n{def_.name} :: {sig}\n```\n\n*{kindStr}* from `{def_.moduleName}`"
  | none =>
      s!"**{def_.name}**\n\n*{kindStr}* from `{def_.moduleName}`"

/-- Convert compiler SymbolKind to LSP SymbolKind for display -/
def compilerSymbolKindToString : Soma.Project.SymbolKind → String
  | .binding => "function"
  | .dataCon _ _ => "constructor"
  | .type => "type"
  | .typeClass => "class"
  | .typeClassMethod _ => "method"
  | .instanceMethod _ _ => "instance method"
  | .letBinding => "local binding"
  | .lambdaParam => "parameter"
  | .patternVar => "variable"
  | .patternAs => "variable"
  | .composeBinding => "local binding"
  | .intrinsicBinding => "intrinsic"
  | .intrinsicType => "intrinsic type"

/-- Format hover content for an external symbol (from seedSymbols) -/
def formatExternalSymbolHover (sym : Symbol) (ty : Value) : String :=
  let kindStr := compilerSymbolKindToString sym.kind
  let typeStr := valueToString ty
  s!"```soma\n{sym.name} :: {typeStr}\n```\n\n*{kindStr}* from `{sym.module}`"

/-- Look up a name in seedSymbols -/
def lookupInSeedSymbols (name : String) (seedSymbols : SymbolEnv) : Option (Symbol × Value) :=
  seedSymbols.toArray.find? fun (sym, _) => sym.name == name

/-- Format hover for a keyword -/
def formatKeywordHover (kind : TokenKind) (text : String) : String :=
  let desc := match kind with
    | .kw_def => "Define a function or value"
    | .kw_let => "Local binding"
    | .kw_in => "Body of let expression"
    | .kw_case => "Pattern matching"
    | .kw_if => "Conditional expression"
    | .kw_then => "Then branch of if"
    | .kw_else => "Else branch of if"
    | .kw_inductive => "Define an inductive type"
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
    | _ => kind.describe
  s!"**{text}** — {desc}"

/-- Format hover for a syntax construct -/
def formatSyntaxHover (kind : SyntaxKind) (text : String) : String :=
  let preview := if text.length > 50 then (text.take 50 |>.copy) ++ "..." else text
  s!"*{kind.describe}*\n```soma\n{preview}\n```"

/-- Get hover information at a position -/
def getHoverAt (offset : Nat) (mod : CompiledModule) (allModules : Array CompiledModule)
    (seedSymbols : SymbolEnv := {}) : Option (String × Span) := do
  let nodeInfo ← findNodeAtPosition offset mod.tree

  guard (!nodeInfo.node.green.isTrivia)
  if nodeInfo.node.syntaxKind? == some .triviaToken then none else

  let span := mod.tree.spanOf nodeInfo.node

  -- Check if it's a token
  if nodeInfo.node.isToken then
    let text ← nodeInfo.node.text?
    let kind ← nodeInfo.node.tokenKind?

    if kind.isNameLike then
      if let some local_ := mod.scopeMap.resolveByNodeId nodeInfo.node.id then
        return (formatLocalBindingHover local_, span)
      if let some local_ := mod.scopeMap.resolve text offset then
        return (formatLocalBindingHover local_, span)
      -- Try to find definition in current module
      if let some def_ := mod.symbols.lookupDefinition text then
        return (formatDefinitionHover def_ mod.globals, span)
      -- Try other open modules (for imported symbols)
      for other in allModules do
        if let some def_ := other.symbols.lookupDefinition text then
          return (formatDefinitionHover def_ other.globals, span)
      -- Try external dependencies (seedSymbols)
      if let some (sym, ty) := lookupInSeedSymbols text seedSymbols then
        return (formatExternalSymbolHover sym ty, span)
      -- Unknown identifier/operator
      return (s!"**{text}** — *unknown*", span)
    else if kind.isKeyword then
      return (formatKeywordHover kind text, span)
    else
      -- Punctuation
      return (s!"`{text}` — {kind.describe}", span)
  else
    -- Interior node
    if let some kind := nodeInfo.node.syntaxKind? then
      match nodeInfo.node.green with
      | .error msg _ _ =>
          return (s!"**Error** at {span.start.line}:{span.start.column}\n\n{msg}", span)
      | .missing expected =>
          return (s!"**Missing** at {span.start.line}:{span.start.column}\n\nExpected: {expected.describe}", span)
      | _ =>
          let text := nodeText mod.tree nodeInfo.node
          return (formatSyntaxHover kind text, span)
    else
      none

/-- Find definition location for a name -/
def findDefinitionLocation (name : String) (mod : CompiledModule) (allModules : Array CompiledModule)
    (seedSymbols : SymbolEnv := {}) : Option (String × Span) := do
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

  -- Try external dependencies (seedSymbols)
  -- Note: External symbols have source spans but we need to find the file path
  -- The Symbol.module field contains the module name, we need to map it to a file
  if let some (sym, _) := lookupInSeedSymbols name seedSymbols then
    -- For external deps, we construct the path from package/module info
    -- The span already contains location info from the metadata
    -- We need to find the actual source file - for now use module as path hint
    -- TODO: Improve this by storing file paths in external dependency metadata
    return (sym.module ++ ".soma", sym.span)

  none

/-- Get definition at a position -/
def getDefinitionAt (offset : Nat) (mod : CompiledModule) (allModules : Array CompiledModule)
    (seedSymbols : SymbolEnv := {}) : Option (String × Span) := do
  let nodeInfo ← findNodeAtPosition offset mod.tree

  if nodeInfo.node.isToken then
    let kind ← nodeInfo.node.tokenKind?
    if kind.isNameLike then
      let text ← nodeInfo.node.text?
      if let some local_ := mod.scopeMap.resolveByNodeId nodeInfo.node.id then
        return (mod.filePath, local_.nameSpan)
      if let some local_ := mod.scopeMap.resolve text offset then
        return (mod.filePath, local_.nameSpan)
      findDefinitionLocation text mod allModules seedSymbols
    else
      none
  else
    none

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
  let otherModules := allModules.filter (·.filePath != mod.filePath)
  match context with
  | .inTypeExpr | .inTypeSignature | .afterColon =>
      -- Only type names and type variables
      let localTypes := mod.symbols.definitionsOfKind .type
      let localTyVars := mod.symbols.definitionsOfKind .typeVariable
      let importedTypes := otherModules.foldl (fun acc m =>
        acc ++ m.symbols.definitionsOfKind .type) #[]
      localTypes ++ localTyVars ++ importedTypes

  | .inPattern =>
      -- Constructors and variables
      let constructors := mod.symbols.definitionsOfKind .constructor
      let variables := mod.symbols.definitionsOfKind .variable
      let importedCons := otherModules.foldl (fun acc m =>
        acc ++ m.symbols.definitionsOfKind .constructor) #[]
      constructors ++ variables ++ importedCons

  | .afterDot _ =>
      -- TODO: Field completions based on parent type
      mod.symbols.definitionsOfKind .field

  | .inImport | .inImportItems =>
      -- Module names (not implemented yet)
      #[]

  | _ =>
      -- All symbols
      let local_ := mod.symbols.allDefinitions
      let imported := otherModules.foldl (fun acc m =>
        acc ++ m.symbols.allDefinitions) #[]
      local_ ++ imported

/-- Get all completions at a position -/
def getCompletionsAt (offset : Nat) (mod : CompiledModule) (allModules : Array CompiledModule)
    : Array DefinitionSite :=
  let context := match findNodeAtPosition offset mod.tree with
    | some nodeInfo => nodeInfo.context
    | none => .unknown
  getCompletionsForContext context mod allModules

/-- Try to find a local binding at the given offset (either in scope or at binding site) -/
private def resolveLocalBinding (name : String) (offset : Nat) (mod : CompiledModule)
    : Option LocalBinding :=
  -- Try in-scope resolution first
  if let some local_ := mod.scopeMap.resolve name offset then
    some local_
  else
    -- Try binding-site resolution (cursor is on the definition)
    mod.scopeMap.bindings.find? fun b =>
      b.name == name &&
      offset >= b.nameSpan.start.byteOffset &&
      offset < b.nameSpan.stop.byteOffset

/-- Find all references to a name in a module -/
def findReferencesInModule (name : String) (mod : CompiledModule)
    (targetOffset : Option Nat := none) : Array Span :=
  match targetOffset with
  | some offset =>
    if let some local_ := resolveLocalBinding name offset mod then
      mod.scopeMap.findLocalReferences local_ mod.tree
    else
      (mod.symbols.getReferences name).map (·.span)
  | none =>
    (mod.symbols.getReferences name).map (·.span)

/-- Find all references across modules -/
def findAllReferences (name : String) (allModules : Array CompiledModule)
    (targetOffset : Option Nat := none)
    : Array (String × Span) :=
  allModules.foldl (fun acc mod =>
    let refs := findReferencesInModule name mod targetOffset
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
