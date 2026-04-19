import Lapis
import Lsp.State
import Lsp.Analysis
import Lsp.Symbols
import Lsp.Loc
import Lsp.Haoma
import Lsp.SemanticTokens
import Soma.Project.Check
import Soma.Project.Graph

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
open Soma.Syntax (SourceFile)
open Soma.Dependent (Globals InstanceEnv AbbrevEnv)
open Soma.Project (ModuleGraph ModuleInfo buildDependencyGraph
  topoSortModules TopoSortResult preludeModuleName SymbolEnv)
open Soma.Project.Check (CheckedModule parseModuleFile parseModuleFiles checkModule
  checkModulesInOrder mergeGlobals extractPreludeSymbols)

/-- Format the body of a Soma diagnostic for LSP display -/
private def renderDiagMessage (diag : Soma.Syntax.Diagnostic) : String :=
  let codePrefix := match diag.code with
    | some c => s!"[{c}] "
    | none => ""
  let primaryLine := if diag.primaryLabel.message.isEmpty
      || diag.primaryLabel.message == diag.message then ""
    else s!"\n{diag.primaryLabel.message}"
  let noteLines := diag.notes.foldl (fun acc n => acc ++ "\n" ++ "note: " ++ n) ""
  let helpLine := match diag.help with
    | some h => s!"\nhelp: {h}"
    | none => ""
  s!"{codePrefix}{diag.message}{primaryLine}{noteLines}{helpLine}"

/-- Build LSP `DiagnosticRelatedInformation` for each secondary label -/
private def secondaryLabelsToRelated (sf : SourceFile) (uri : String)
    (labels : Array Soma.Syntax.Label) : Array DiagnosticRelatedInformation :=
  labels.map fun lbl =>
    { location := { uri, range := spanToRange sf lbl.span }
    , message := if lbl.message.isEmpty then "related" else lbl.message }

/-- Convert Soma diagnostics to LSP format -/
def convertDiagnostics (sf : SourceFile) (uri : String) (diags : Soma.Syntax.Diagnostics)
    : Array Diagnostic :=
  diags.map fun diag =>
    let range := spanToRange sf diag.span
    let related := secondaryLabelsToRelated sf uri diag.secondaryLabels
    { range := range
    , severity := some (match diag.severity with
        | .error => .error
        | .warning => .warning
        | .info => .information
        | .hint => .hint)
    , code := diag.code
    , source := some "soma"
    , message := renderDiagMessage diag
    , relatedInformation := if related.isEmpty then none else some related
    : Diagnostic }

/-- Load a single haoma project: discover modules, parse, and type-check all from source -/
def loadHaomaProject (ctx : RequestContext LspState) (projectRoot : System.FilePath) : IO Bool := do
  match ← Haoma.loadMetadata projectRoot with
  | .ok metadata =>
    let modulePairs := metadata.modules.map fun m =>
      (m.name, System.FilePath.mk m.path)

    let (parseDiags, graph, _sourceMap) ← parseModuleFiles modulePairs

    if !parseDiags.isEmpty then
      ctx.logInfo s!"Parse diagnostics: {parseDiags.size}"

    let depGraph := buildDependencyGraph graph
    let depGraph := if graph.contains preludeModuleName then
      let preludeDepsSet := Id.run do
        let mut visited : Std.HashSet String := {}
        let mut worklist : Array String := #[preludeModuleName]
        while !worklist.isEmpty do
          let current := worklist[0]!
          worklist := worklist.extract 1 worklist.size
          if visited.contains current then continue
          visited := visited.insert current
          let edges := depGraph.get? current |>.getD #[]
          for e in edges do
            if !visited.contains e.targetModule then
              worklist := worklist.push e.targetModule
        visited
      depGraph.fold (init := depGraph) fun acc modName edges =>
        if preludeDepsSet.contains modName then acc
        else
          let hasPreludeDep := edges.any (·.targetModule == preludeModuleName)
          if hasPreludeDep then acc
          else acc.insert modName (edges.push { targetModule := preludeModuleName, importSpan := Soma.Syntax.Span.uninhabited })
    else depGraph
    let sortedNames : Array String := match topoSortModules depGraph with
      | .sorted order => order
      | .cycles _cycles =>
        modulePairs.map (Prod.fst)

    let packageName := metadata.root_package

    let state ← ctx.getUserState
    let supply := state.projectSupply
    let emptySymbols : SymbolEnv := Inhabited.default

    let preludeSyms : Array String :=
      match sortedNames.findIdx? (· == preludeModuleName) with
      | some idx =>
        let prefixNames := sortedNames.extract 0 (idx + 1)
        let (_, prefixResults, _) := checkModulesInOrder prefixNames graph
          Globals.empty InstanceEnv.empty AbbrevEnv.empty emptySymbols packageName supply #[]
        match prefixResults.find? (·.name == preludeModuleName) with
        | some preludeCm =>
          let ps : SymbolEnv := preludeCm.publicSymbols
          ps.toArray.map fun p => p.1.name
        | none => #[]
      | none => #[]

    let (_checkDiags, checkedResults, finalSupply) :=
      checkModulesInOrder sortedNames graph Globals.empty InstanceEnv.empty AbbrevEnv.empty
        emptySymbols packageName supply preludeSyms

    let checkedMap : Std.HashMap String CheckedModule := checkedResults.foldl (init := {})
      fun acc (cm : CheckedModule) => acc.insert cm.name cm

    ctx.modifyUserState fun s =>
      let s' := s.addHaomaProject metadata
      let existingSet := s'.topoOrder.foldl (init := ({} : Std.HashSet String)) fun acc n => acc.insert n
      let newEntries := sortedNames.filter fun n => !existingSet.contains n
      let mergedOrder := s'.topoOrder ++ newEntries
      { s' with
        checkedModules := checkedMap.fold (init := s'.checkedModules) fun acc k v => acc.insert k v
        moduleGraph := graph.fold (init := s'.moduleGraph) fun acc k v => acc.insert k v
        topoOrder := mergedOrder
        projectSupply := finalSupply
        preludeSymbols := if preludeSyms.isEmpty then s'.preludeSymbols else preludeSyms }

    ctx.logInfo s!"Loaded {checkedResults.size}/{modulePairs.size} modules from {packageName}"
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

/-- Look up the module name for a file path and compute its checked deps -/
private def depsForFile (state : LspState) (filePath : String) : Std.HashMap String CheckedModule :=
  match state.nameForPath filePath with
  | some name => state.checkedDepsForModule name
  | none => {}

/-- Handle textDocument/didOpen -/
def handleDidOpen (ctx : RequestContext LspState) (params : DidOpenTextDocumentParams) : IO Unit := do
  let uri := params.textDocument.uri
  let content := params.textDocument.text
  let filePath := normalizePath (uriToPath uri)
  let version := params.textDocument.version

  -- Lazy discovery: try to load haoma project if file is not in a known project
  tryDiscoverProjectForFile ctx filePath

  let state ← ctx.getUserState
  let modName? := state.nameForPath filePath
  let checkedDeps := depsForFile state filePath

  let existingChecked := modName?.bind state.checkedModules.get?
  let mod := analyzeSource filePath content none checkedDeps state.preludeSymbols modName? existingChecked

  -- Update state
  ctx.modifyUserState fun s =>
    s.setModule filePath mod
     |>.registerModulePath mod.name filePath
     |>.registerModuleUri mod.name uri

  -- Publish diagnostics immediately on open
  let lspDiags := convertDiagnostics mod.sourceFile uri mod.diagnostics
  ctx.publishDiagnostics { uri, version := some version, diagnostics := lspDiags }

  ctx.logInfo s!"Opened: {uri} ({mod.symbols.allNames.size} symbols, {mod.diagnostics.size} diagnostics)"

/-- Handle textDocument/didChange -/
def handleDidChange (ctx : RequestContext LspState) (params : DidChangeTextDocumentParams) : IO Unit := do
  let uri := params.textDocument.uri
  let filePath := normalizePath (uriToPath uri)

  -- Get updated content from VFS
  let some content ← ctx.getDocumentContent uri | return

  -- Get old module for incremental analysis
  let state ← ctx.getUserState
  let oldModule? := state.getModule filePath
  let modName? := state.nameForPath filePath
  let checkedDeps := depsForFile state filePath

  -- Incremental analysis (reuses NodeIds and symbols where possible)
  let mod := analyzeSource filePath content oldModule? checkedDeps state.preludeSymbols modName?

  -- Extract imported modules from the analyzed module
  let importedModules := extractImportedModules mod.symbols

  -- Update state: module, path mapping, and reverse dependencies
  ctx.modifyUserState fun s =>
    s.setModule filePath mod
     |>.registerModulePath mod.name filePath
     |>.registerModuleUri mod.name uri
     |>.updateReverseDeps mod.name importedModules

  -- Get version for diagnostics
  let some snap ← ctx.getDocument uri | return
  let version := snap.version

  -- Publish diagnostics for the changed module
  let lspDiags := convertDiagnostics mod.sourceFile uri mod.diagnostics
  ctx.publishDiagnostics { uri, version := some version, diagnostics := lspDiags }

  -- Find and re-analyze dependent modules
  let state' ← ctx.getUserState
  let dependentModuleNames := state'.getTransitiveDependents mod.name

  for depModName in dependentModuleNames do
    if let some depUri := state'.getModuleUri depModName then
      if let some depFilePath := state'.getModulePath depModName then
        if let some depContent ← ctx.getDocumentContent depUri then
          let depOldModule? := state'.getModule depFilePath
          let depCheckedDeps := state'.checkedDepsForModule depModName
          let depMod := analyzeSource depFilePath depContent depOldModule? depCheckedDeps state'.preludeSymbols (some depModName)

          ctx.modifyUserState fun s => s.setModule depFilePath depMod

          let depLspDiags := convertDiagnostics depMod.sourceFile depUri depMod.diagnostics
          ctx.publishDiagnostics { uri := depUri, diagnostics := depLspDiags }

/-- Handle textDocument/didClose -/
def handleDidClose (ctx : RequestContext LspState) (params : DidCloseTextDocumentParams) : IO Unit := do
  let uri := params.textDocument.uri
  let filePath := normalizePath (uriToPath uri)

  -- Remove from state
  ctx.modifyUserState fun s => s.removeModule filePath

  -- Clear diagnostics (TODO: review this decision)
  ctx.publishDiagnostics { uri, diagnostics := #[] }

  ctx.logInfo s!"Closed: {uri}"

/-- Handle textDocument/didSave -/
def handleDidSave (ctx : RequestContext LspState) (params : DidSaveTextDocumentParams) : IO Unit := do
  let uri := params.textDocument.uri
  let filePath := normalizePath (uriToPath uri)

  -- On save, do full analysis and publish all diagnostics
  let some content ← ctx.getDocumentContent uri | return
  let state ← ctx.getUserState
  let modName? := state.nameForPath filePath
  let checkedDeps := depsForFile state filePath
  let mod := analyzeSource filePath content none checkedDeps state.preludeSymbols modName?

  ctx.modifyUserState fun s =>
    s.setModule filePath mod
     |>.registerModulePath mod.name filePath
     |>.registerModuleUri mod.name uri

  let lspDiags := convertDiagnostics mod.sourceFile uri mod.diagnostics
  let some snap ← ctx.getDocument uri | return
  ctx.publishDiagnostics { uri, version := some snap.version, diagnostics := lspDiags }

  ctx.logInfo s!"Saved: {uri} ({mod.diagnostics.size} diagnostics)"

/-- Handle textDocument/hover -/
def handleHover (ctx : RequestContext LspState) (params : HoverParams) : IO (Option Hover) := do
  let uri := params.textDocument.uri
  let filePath := normalizePath (uriToPath uri)

  -- Get cached module (never reanalyze here)
  let state ← ctx.getUserState
  let some mod := state.getModule filePath | return none

  -- Convert position to byte offset
  let offset := positionToOffset mod.sourceFile params.position

  -- Get all modules for cross-reference lookup
  let allMods := state.allModules

  -- Build seed symbols from checked dependencies for this module
  let seedSymbols := state.seedSymbolsForModule mod.name

  -- Get hover content (uses cached symbol table and checked deps)
  let some (hoverText, hoverSpan) := getHoverAt offset mod allMods seedSymbols | return none

  return some {
    contents := { kind := .markdown, value := hoverText }
    range := some (spanToRange mod.sourceFile hoverSpan)
  }

/-- Handle textDocument/definition -/
def handleDefinition (ctx : RequestContext LspState) (params : TextDocumentPositionParams) : IO (Option Location) := do
  ctx.logInfo "definition: start"

  let uri := params.textDocument.uri
  let filePath := normalizePath (uriToPath uri)
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

  -- Build seed symbols from checked dependencies for this module
  let seedSymbols := state.seedSymbolsForModule mod.name

  -- Find definition (uses cached symbol table and checked deps)
  let some (defPath, defSpan) := getDefinitionAt offset mod allMods seedSymbols | do
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
  let filePath := normalizePath (uriToPath uri)

  -- Get cached module (never re-analyze here)
  let state ← ctx.getUserState
  let some mod := state.getModule filePath | return { isIncomplete := false, items := #[] }

  -- Convert position to byte offset
  let offset := positionToOffset mod.sourceFile params.position

  -- Get live content from VFS (has latest keystrokes even before didChange analysis)
  let liveContent ← ctx.getDocumentContent uri

  let isTriggerChar := match params.context with
    | some ctx => match ctx.triggerKind with
      | .triggerCharacter => true
      | _ => false
    | none => false
  if isTriggerChar == true then
    if let some live := liveContent then
      let lines := (live.splitOn "\n").toArray
      let lineIdx := params.position.line
      if h : lineIdx < lines.size then
        let line := lines[lineIdx]
        let col := params.position.character
        let prevChar := if col >= 2 then line.get ⟨col - 2⟩ else ' '
        let lastChar := if col >= 1 then line.get ⟨col - 1⟩ else ' '
        if lastChar == ':' && prevChar != ':' then
          return { isIncomplete := false, items := #[] }

  -- Get all modules
  let allMods := state.allModules

  -- Get completions (Globals-based with CST fallback, namespace-aware)
  let completions := getCompletionsAt offset mod allMods (some state) liveContent
    (some params.position.line) (some params.position.character)

  -- Convert to completion items
  let items := completions.map fun entry =>
    { label := entry.label
    , kind := some (match completionKindNumber entry.kind with
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
    , detail := entry.detail
    , documentation := none
    , insertText := some entry.insertText
    : CompletionItem }

  return { isIncomplete := false, items }

/-- Handle textDocument/documentSymbol -/
def handleDocumentSymbol (ctx : RequestContext LspState) (params : Lean.Json) : IO Lean.Json := do
  let uri := (do
    let td ← params.getObjVal? "textDocument"
    td.getObjValAs? String "uri"
  ) |>.toOption |>.getD ""

  let filePath := normalizePath (uriToPath uri)

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
  let filePath := normalizePath (uriToPath uri)

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
  let filePath := normalizePath (uriToPath uri)

  let state ← ctx.getUserState
  let some mod := state.getModule filePath | return emptyTokens

  return buildSemanticTokens mod

open Lapis.Protocol.Generated in
def handleInlayHint (ctx : RequestContext LspState) (params : InlayHintParams)
    : IO (Array InlayHint) := do
  let uri := params.textDocument.uri
  let filePath := normalizePath (uriToPath uri)

  let state ← ctx.getUserState
  let some mod := state.getModule filePath | return #[]

  let sf := mod.sourceFile
  let startOffset := positionToOffset sf params.range.start
  let endOffset := positionToOffset sf params.range.«end»

  let hints := collectInlayHints mod startOffset endOffset

  return hints.map fun (span, label, _) =>
    let pos := offsetToPosition sf span.stop.byteOffset
    { position := pos
    , label := Lean.Json.str label
    , kind := some .type
    , paddingLeft := some true
    , paddingRight := some false
    : InlayHint }

open Lapis.Protocol.Generated in
def handleSignatureHelp (ctx : RequestContext LspState) (params : SignatureHelpParams)
    : IO (Option SignatureHelp) := do
  let uri := params.textDocument.uri
  let filePath := normalizePath (uriToPath uri)

  let state ← ctx.getUserState
  let some mod := state.getModule filePath | return none

  let offset := positionToOffset mod.sourceFile params.position
  let allMods := state.allModules
  let seedSymbols := state.seedSymbolsForModule mod.name

  let some (sigInfo, activeParam) := getSignatureHelpAt offset mod allMods seedSymbols | return none

  let paramInfos := sigInfo.parameters.map fun (name, ty) =>
    { label := Lean.Json.str s!"{name} :: {ty}"
    , documentation := Lean.Json.null
    : ParameterInformation }

  return some {
    signatures := #[{
      label := sigInfo.fullSignature
      , parameters := some paramInfos
      , activeParameter := some activeParam
    }]
    , activeSignature := some 0
    , activeParameter := some activeParam
  }

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
  , signatureHelpProvider := some {
      triggerCharacters := some #["(", " "]
    }
  , definitionProvider := some true
  , referencesProvider := some true
  , documentSymbolProvider := some true
  , inlayHintProvider := some { resolveProvider := some false }
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
    |>.onRequest "textDocument/inlayHint" handleInlayHint
    |>.onRequestOpt "textDocument/signatureHelp" handleSignatureHelp

  runStdio config ({} : LspState)

end Lsp

def main : IO Unit := Lsp.main
