import Lapis
import Lsp.State
import Lsp.Analysis
import Lsp.Symbols
import Lsp.Loc
import Lsp.Haoma
import Lsp.SemanticTokens
import Soma.Project.Metadata

namespace Lsp

open Lapis.Protocol.Types
open Lapis.Protocol.Messages
open Lapis.Protocol.Capabilities
open Lapis.Concurrent.LspActor
open Lapis.Concurrent.Dispatcher
open Lapis.Concurrent.VfsActor
open Lapis.Server.Diagnostics
open Lapis.Server.Progress
open Lapis.Server.SemanticTokens
open Lapis.Protocol.Generated (SemanticTokensParams)
open Soma.Project.Metadata (loadMetadataFromFile)
open Soma.Syntax (SourceFile)

/-- Convert Soma diagnostics to LSP format -/
def convertDiagnostics (sf : SourceFile) (diags : Soma.Syntax.Diagnostics) : Array Diagnostic :=
  diags.map fun diag =>
    let range := spanToRange sf diag.span
    { range := range
    , severity := some (match diag.severity with
        | .error => .error
        | .warning => .warning
        | .info => .information
        | .hint => .hint)
    , source := some "soma"
    , message := diag.message
    : Diagnostic }

/-- Load a single haoma project with logging, including dependency metadata -/
def loadHaomaProject (ctx : RequestContext LspState) (projectRoot : System.FilePath) : IO Bool := do
  -- Use --full to generate type metadata for dependencies
  match ← Haoma.loadMetadataFull projectRoot with
  | .ok metadata =>
    -- Load external dependency metadata from the type_metadata paths
    let mut deps : Array Soma.Project.Check.ExternalDependency := #[]
    for (depName, metaPath) in metadata.type_metadata.toArray do
      -- Skip root package metadata
      if depName == metadata.root_package then
        continue
      -- Resolve relative paths against project root
      let path := if metaPath.startsWith "/" then
        System.FilePath.mk metaPath
      else
        projectRoot / metaPath
      match ← loadMetadataFromFile path with
      | .ok dep =>
        deps := deps.push dep
      | .error e =>
        ctx.logError s!"Failed to load dependency {depName} from {path}: {e}"

    ctx.modifyUserState fun s =>
      let s' := s.addHaomaProject metadata
      let s'' := s'.addExternalDeps deps
      s''
    return true
  | .notHaomaProject =>
    return false
  | .error msg =>
    ctx.logInfo s!"Failed to load haoma metadata for {projectRoot}: {msg}"
    return false

/-- Try to discover and load haoma project for a file (lazy discovery) -/
def tryDiscoverProjectForFile (ctx : RequestContext LspState) (filePath : String) : IO Unit := do
  let state ← ctx.getUserState

  -- Skip if file is already in a known project
  if state.isFileInKnownProject filePath then
    return

  -- Try to find a haoma project root for this file
  let filePathObj := System.FilePath.mk filePath
  match ← Haoma.findProjectRoot filePathObj with
  | none => return -- Not in a haoma project
  | some projectRoot =>
    -- Check if we already know this project
    if state.hasProjectRoot projectRoot.toString then
      return

    -- Discover new project with progress
    ctx.withProgress "Loading haoma project" (cancellable := false) fun progress => do
      progress.report (message := some s!"Loading {projectRoot.fileName.getD "project"}...")
      let _ ← loadHaomaProject ctx projectRoot
      progress.report (message := some "Done") (percentage := some 100)

/-- Handle textDocument/didOpen -/
def handleDidOpen (ctx : RequestContext LspState) (params : DidOpenTextDocumentParams) : IO Unit := do
  let uri := params.textDocument.uri
  let content := params.textDocument.text
  let filePath := uriToPath uri
  let version := params.textDocument.version

  -- Lazy discovery: try to load haoma project if file is not in a known project
  tryDiscoverProjectForFile ctx filePath

  let state ← ctx.getUserState
  let mod := analyzeSource filePath content none state.seedGlobals state.seedInstanceEnv state.seedAbbrevEnv state.seedSymbols

  -- Update state
  ctx.modifyUserState fun s => s.setModule filePath mod

  -- Publish diagnostics immediately on open
  let lspDiags := convertDiagnostics mod.sourceFile mod.diagnostics
  ctx.publishDiagnostics { uri, version := some version, diagnostics := lspDiags }

  ctx.logInfo s!"Opened: {uri} ({mod.symbols.allNames.size} symbols, {mod.diagnostics.size} diagnostics)"

/-- Handle textDocument/didChange -/
def handleDidChange (ctx : RequestContext LspState) (params : DidChangeTextDocumentParams) : IO Unit := do
  let uri := params.textDocument.uri
  let filePath := uriToPath uri

  -- Get updated content from VFS
  let some content ← ctx.getDocumentContent uri | return

  -- Get old module for incremental analysis
  let state ← ctx.getUserState
  let oldModule? := state.getModule filePath

  -- Incremental analysis (reuses NodeIds and symbols where possible)
  let mod := analyzeSource filePath content oldModule? state.seedGlobals state.seedInstanceEnv state.seedAbbrevEnv state.seedSymbols

  -- Extract imported modules from the analyzed module
  let importedModules := extractImportedModules mod.symbols

  -- Update state: module, path mapping, and reverse dependencies
  ctx.modifyUserState fun s =>
    let s' := s.setModule filePath mod
    let s'' := s'.registerModulePath mod.name filePath
    s''.updateReverseDeps mod.name importedModules

  -- Get version for diagnostics
  let some snap ← ctx.getDocument uri | return
  let version := snap.version

  -- Publish diagnostics for the changed module
  let lspDiags := convertDiagnostics mod.sourceFile mod.diagnostics
  ctx.publishDiagnostics { uri, version := some version, diagnostics := lspDiags }

  -- Find and re-analyze dependent modules
  let state' ← ctx.getUserState
  let dependentModuleNames := state'.getTransitiveDependents mod.name

  for depModName in dependentModuleNames do
    -- Get the file path for this dependent module
    if let some depFilePath := state'.getModulePath depModName then
      -- Get the content of the dependent file
      let depUri := pathToUri depFilePath
      if let some depContent ← ctx.getDocumentContent depUri then
        -- Get old module for incremental analysis
        let depOldModule? := state'.getModule depFilePath

        -- Re-analyze with the dependent module marked as needing re-check
        -- The incremental analysis will detect that imported modules changed
        let depMod := analyzeSource depFilePath depContent depOldModule? state'.seedGlobals state'.seedInstanceEnv state'.seedAbbrevEnv state'.seedSymbols

        -- Update state
        ctx.modifyUserState fun s => s.setModule depFilePath depMod

        -- Publish diagnostics for the dependent module
        let depLspDiags := convertDiagnostics depMod.sourceFile depMod.diagnostics
        ctx.publishDiagnostics { uri := depUri, diagnostics := depLspDiags }

/-- Handle textDocument/didClose -/
def handleDidClose (ctx : RequestContext LspState) (params : DidCloseTextDocumentParams) : IO Unit := do
  let uri := params.textDocument.uri
  let filePath := uriToPath uri

  -- Remove from state
  ctx.modifyUserState fun s => s.removeModule filePath

  -- Clear diagnostics (TODO: review this decision)
  ctx.publishDiagnostics { uri, diagnostics := #[] }

  ctx.logInfo s!"Closed: {uri}"

/-- Handle textDocument/didSave -/
def handleDidSave (ctx : RequestContext LspState) (params : DidSaveTextDocumentParams) : IO Unit := do
  let uri := params.textDocument.uri
  let filePath := uriToPath uri

  -- On save, do full analysis and publish all diagnostics
  let some content ← ctx.getDocumentContent uri | return
  let state ← ctx.getUserState
  let mod := analyzeSource filePath content none state.seedGlobals state.seedInstanceEnv state.seedAbbrevEnv state.seedSymbols

  ctx.modifyUserState fun s => s.setModule filePath mod

  let lspDiags := convertDiagnostics mod.sourceFile mod.diagnostics
  let some snap ← ctx.getDocument uri | return
  ctx.publishDiagnostics { uri, version := some snap.version, diagnostics := lspDiags }

  ctx.logInfo s!"Saved: {uri} ({mod.diagnostics.size} diagnostics)"

/-- Handle textDocument/hover -/
def handleHover (ctx : RequestContext LspState) (params : HoverParams) : IO (Option Hover) := do
  let uri := params.textDocument.uri
  let filePath := uriToPath uri

  -- Get cached module (never reanalyze here)
  let state ← ctx.getUserState
  let some mod := state.getModule filePath | return none

  -- Convert position to byte offset
  let offset := positionToOffset mod.sourceFile params.position

  -- Get all modules for cross-reference lookup
  let allMods := state.allModules

  -- Get hover content (uses cached symbol table and external deps)
  let some (hoverText, hoverSpan) := getHoverAt offset mod allMods state.seedSymbols | return none

  return some {
    contents := { kind := .markdown, value := hoverText }
    range := some (spanToRange mod.sourceFile hoverSpan)
  }

/-- Handle textDocument/definition -/
def handleDefinition (ctx : RequestContext LspState) (params : TextDocumentPositionParams) : IO (Option Location) := do
  ctx.logInfo "definition: start"

  let uri := params.textDocument.uri
  let filePath := uriToPath uri
  ctx.logInfo s!"definition: uri={uri}"

  -- Get cached module (never re-analyze here)
  let state ← ctx.getUserState
  let some mod := state.getModule filePath | do
    ctx.logInfo "definition: no module found"
    return none

  -- Convert position to byte offset
  let offset := positionToOffset mod.sourceFile params.position
  ctx.logInfo s!"definition: offset={offset}"

  -- Get all modules
  let allMods := state.allModules
  ctx.logInfo s!"definition: allMods.size={allMods.size}"

  -- Find definition (uses cached symbol table and external deps)
  let some (defPath, defSpan) := getDefinitionAt offset mod allMods state.seedSymbols | do
    ctx.logInfo "definition: no definition found"
    return none

  ctx.logInfo s!"definition: found at {defPath}"
  let targetSf := if defPath == filePath then mod.sourceFile
    else match state.allModules.find? (·.filePath == defPath) with
      | some targetMod => targetMod.sourceFile
      | none => mod.sourceFile
  return some {
    uri := pathToUri defPath
    range := spanToRange targetSf defSpan
  }

/-- Handle textDocument/completion -/
def handleCompletion (ctx : RequestContext LspState) (params : CompletionParams) : IO CompletionList := do
  let uri := params.textDocument.uri
  let filePath := uriToPath uri

  -- Get cached module (never re-analyze here)
  let state ← ctx.getUserState
  let some mod := state.getModule filePath | return { isIncomplete := false, items := #[] }

  -- Convert position to byte offset
  let offset := positionToOffset mod.sourceFile params.position

  -- Get all modules
  let allMods := state.allModules

  -- Get completions (uses cached symbol table)
  let defs := getCompletionsAt offset mod allMods

  -- Convert to completion items
  let items := defs.map fun def_ =>
    { label := def_.name
    , kind := some (match completionKindNumber def_.kind with
        | 2 => .method
        | 3 => .function
        | 4 => .constructor
        | 5 => .field
        | 6 => .variable
        | 8 => .interface
        | 9 => .module
        | 22 => .struct
        | 25 => .typeParameter
        | _ => .text)
    , detail := def_.typeSignature
    , documentation := none
    , insertText := some def_.name
    : CompletionItem }

  return { isIncomplete := false, items }

/-- Handle textDocument/documentSymbol -/
def handleDocumentSymbol (ctx : RequestContext LspState) (params : Lean.Json) : IO Lean.Json := do
  let uri := (do
    let td ← params.getObjVal? "textDocument"
    td.getObjValAs? String "uri"
  ) |>.toOption |>.getD ""

  let filePath := uriToPath uri

  -- Get cached module
  let state ← ctx.getUserState
  let some mod := state.getModule filePath | return Lean.Json.arr #[]

  -- Get symbols (from cache)
  let symbols := getDocumentSymbols mod

  -- Convert to JSON
  let sf := mod.sourceFile
  let symbolInfos := symbols.map fun def_ =>
    let range := spanToRange sf def_.declSpan
    let selectionRange := spanToRange sf def_.nameSpan
    Lean.Json.mkObj [
      ("name", Lean.Json.str def_.name),
      ("kind", Lean.Json.num (documentSymbolKindNumber def_.kind)),
      ("range", Lean.Json.mkObj [
        ("start", Lean.Json.mkObj [
          ("line", Lean.Json.num range.start.line),
          ("character", Lean.Json.num range.start.character)
        ]),
        ("end", Lean.Json.mkObj [
          ("line", Lean.Json.num range.«end».line),
          ("character", Lean.Json.num range.«end».character)
        ])
      ]),
      ("selectionRange", Lean.Json.mkObj [
        ("start", Lean.Json.mkObj [
          ("line", Lean.Json.num selectionRange.start.line),
          ("character", Lean.Json.num selectionRange.start.character)
        ]),
        ("end", Lean.Json.mkObj [
          ("line", Lean.Json.num selectionRange.«end».line),
          ("character", Lean.Json.num selectionRange.«end».character)
        ])
      ])
    ]

  return Lean.Json.arr symbolInfos

/-- Handle textDocument/references -/
def handleReferences (ctx : RequestContext LspState) (params : ReferenceParams) : IO (Array Location) := do
  let uri := params.textDocument.uri
  let filePath := uriToPath uri

  let state ← ctx.getUserState
  let some mod := state.getModule filePath | return #[]

  let some word := wordAtPosition mod.sourceFile params.position | return #[]
  let offset := positionToOffset mod.sourceFile params.position

  let allMods := state.allModules
  let refs := findAllReferences word allMods (some offset)

  return refs.map fun (path, span) => {
    uri := pathToUri path
    range := spanToRange (
      match state.allModules.find? (·.filePath == path) with
      | some m => m.sourceFile
      | none => mod.sourceFile
    ) span
  }

/-- Handle textDocument/semanticTokens/full -/
def handleSemanticTokensFull (ctx : RequestContext LspState) (params : SemanticTokensParams)
    : IO Lapis.Protocol.Generated.SemanticTokens := do
  let uri := params.textDocument.uri
  let filePath := uriToPath uri

  let state ← ctx.getUserState
  let some mod := state.getModule filePath | return emptyTokens

  return buildSemanticTokens mod

/-- Build server capabilities -/
def serverCapabilities : ServerCapabilities :=
  { textDocumentSync := some {
      openClose := some true
      change := some .full
      save := some { includeText := some false }
    }
  , hoverProvider := some true
  , completionProvider := some {
      triggerCharacters := some #[".", ":"]
      resolveProvider := some false
    }
  , definitionProvider := some true
  , referencesProvider := some true
  , documentSymbolProvider := some true
  , semanticTokensProvider := some defaultOptions
  }

/-- Handle LSP initialization -/
def handleInitialize (ctx : RequestContext LspState) (params : InitializeParams) : IO Unit := do
  let workspaceRoot := params.rootUri.map uriToPath
  match workspaceRoot with
  | none => return
  | some root =>
    ctx.modifyUserState fun s => { s with workspaceRoot := some root }

/-- Handle initialized notification -/
def handleInitialized (ctx : RequestContext LspState) (_params : Lean.Json) : IO Unit := do
  ctx.showInfo "SouLS server initialized"

  let state ← ctx.getUserState
  let some root := state.workspaceRoot | return

  -- Discover all haoma projects in workspace
  ctx.withProgress "Discovering haoma projects" (cancellable := false) fun progress => do
    let workspacePath := System.FilePath.mk root

    progress.report (message := some "Scanning for haoma.kdl files...")
    let projectRoots ← Haoma.discoverProjects workspacePath

    if projectRoots.isEmpty then
      ctx.logInfo "No haoma projects found in workspace"
      return

    ctx.logInfo s!"Found {projectRoots.size} haoma project(s)"

    -- Load metadata for each project
    for h : i in [:projectRoots.size] do
      let projectRoot := projectRoots[i]
      let percentage := (i * 100) / projectRoots.size
      progress.report (message := some s!"Loading {projectRoot.fileName.getD "project"}...") (percentage := some percentage)
      let _ ← loadHaomaProject ctx projectRoot

    progress.report (message := some "Done") (percentage := some 100)

def main : IO Unit := do
  let config : LspConfig LspState := LspConfig.new "souls"
    |>.withVersion "0.1.0"
    |>.withCapabilities serverCapabilities
    |>.onInitialize handleInitialize
    |>.onNotification "initialized" handleInitialized
    |>.onNotification "textDocument/didOpen" handleDidOpen
    |>.onNotification "textDocument/didChange" handleDidChange
    |>.onNotification "textDocument/didClose" handleDidClose
    |>.onNotification "textDocument/didSave" handleDidSave
    |>.onRequestOpt "textDocument/hover" handleHover
    |>.onRequestOpt "textDocument/definition" handleDefinition
    |>.onRequest "textDocument/completion" handleCompletion
    |>.onRequest "textDocument/documentSymbol" handleDocumentSymbol
    |>.onRequest "textDocument/references" handleReferences
    |>.onRequest "textDocument/semanticTokens/full" handleSemanticTokensFull

  runStdio config ({} : LspState)

end Lsp

def main : IO Unit := Lsp.main
