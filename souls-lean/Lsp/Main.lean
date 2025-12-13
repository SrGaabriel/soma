import Lapis
import Lsp.State
import Lsp.Analysis
import Lsp.Symbols
import Lsp.Loc

namespace Lsp

open Lapis.Protocol.Types
open Lapis.Protocol.Messages
open Lapis.Protocol.Capabilities
open Lapis.Concurrent.LspActor
open Lapis.Concurrent.Dispatcher
open Lapis.Concurrent.VfsActor
open Lapis.Server.Diagnostics

/-- Convert Soma diagnostics to LSP format -/
def convertDiagnostics (diags : Soma.Syntax.Diagnostics) : Array Diagnostic :=
  diags.map fun diag =>
    let range := if h : 0 < diag.labels.size then
        spanToRange diag.labels[0].span
      else
        { start := ⟨0, 0⟩, «end» := ⟨0, 0⟩ }
    { range := range
    , severity := some (match diag.severity with
        | .error => .error
        | .warning => .warning
        | .info => .information
        | .hint => .hint)
    , source := some "soma"
    , message := diag.message
    : Diagnostic }

/-- Handle textDocument/didOpen -/
def handleDidOpen (ctx : RequestContext LspState) (params : DidOpenTextDocumentParams) : IO Unit := do
  let uri := params.textDocument.uri
  let content := params.textDocument.text
  let filePath := uriToPath uri

  -- Full analysis on open
  let mod := analyzeSource filePath content

  -- Update state
  ctx.modifyUserState fun s => s.setModule filePath mod

  -- Publish diagnostics immediately on open
  let lspDiags := convertDiagnostics mod.diagnostics
  let some snap ← ctx.getDocument uri | return
  ctx.publishDiagnostics { uri, version := some snap.version, diagnostics := lspDiags }

  ctx.logInfo s!"Opened: {uri} ({mod.symbols.allNames.size} symbols, {mod.diagnostics.size} diagnostics)"

/-- Handle textDocument/didChange -/
def handleDidChange (ctx : RequestContext LspState) (params : DidChangeTextDocumentParams) : IO Unit := do
  let uri := params.textDocument.uri
  let filePath := uriToPath uri

  -- Get updated content from VFS
  let some content ← ctx.getDocumentContent uri | return

  -- Full analysis (debouncing is handled by the LSP framework)
  let mod := analyzeSource filePath content

  -- Update state so hover/definition work
  ctx.modifyUserState fun s => s.setModule filePath mod

  -- Get version for diagnostics
  let some snap ← ctx.getDocument uri | return
  let version := snap.version

  -- Publish all diagnostics (lex, parse, Metal lower, type infer)
  let lspDiags := convertDiagnostics mod.diagnostics
  ctx.publishDiagnostics { uri, version := some version, diagnostics := lspDiags }

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
  let mod := analyzeSource filePath content

  ctx.modifyUserState fun s => s.setModule filePath mod

  let lspDiags := convertDiagnostics mod.diagnostics
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

  -- Get hover content (uses cached symbol table)
  let some hoverText := getHoverAt offset mod allMods | return none

  return some {
    contents := { kind := .markdown, value := hoverText }
    range := none
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

  -- Find definition (uses cached symbol table)
  let some (defPath, defSpan) := getDefinitionAt offset mod allMods | do
    ctx.logInfo "definition: no definition found"
    return none

  ctx.logInfo s!"definition: found at {defPath}"
  return some {
    uri := pathToUri defPath
    range := spanToRange defSpan
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
  let symbolInfos := symbols.map fun def_ =>
    let range := spanToRange def_.declSpan
    let selectionRange := spanToRange def_.nameSpan
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

  let allMods := state.allModules
  let refs := findAllReferences word allMods

  return refs.map fun (path, span) => {
    uri := pathToUri path
    range := spanToRange span
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
  , definitionProvider := some true
  , referencesProvider := some true
  , documentSymbolProvider := some true
  }

def main : IO Unit := do
  let config : LspConfig LspState := LspConfig.new "souls"
    |>.withVersion "0.1.0"
    |>.withCapabilities serverCapabilities
    |>.onNotification "textDocument/didOpen" handleDidOpen
    |>.onNotification "textDocument/didChange" handleDidChange
    |>.onNotification "textDocument/didClose" handleDidClose
    |>.onNotification "textDocument/didSave" handleDidSave
    |>.onRequestOpt "textDocument/hover" handleHover
    |>.onRequestOpt "textDocument/definition" handleDefinition
    |>.onRequest "textDocument/completion" handleCompletion
    |>.onRequest "textDocument/documentSymbol" handleDocumentSymbol
    |>.onRequest "textDocument/references" handleReferences

  runStdio config ({} : LspState)

end Lsp

def main : IO Unit := Lsp.main
