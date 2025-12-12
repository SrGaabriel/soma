import Soma.Syntax
import Lsp.State
import Lsp.Symbols
import Lsp.Loc

namespace Lsp

open Soma.Syntax

/-- Derive module name from file path -/
def moduleNameFromPath (filePath : String) : String :=
  -- Get filename without extension
  let parts := filePath.splitOn "/"
  let fileName := parts.getLast!
  let nameParts := fileName.splitOn "."
  if nameParts.isEmpty then fileName
  else nameParts.head!

/-- Create a unique file ID (simple incrementing counter would be better, but use hash for now) -/
def fileIdFromPath (filePath : String) : FileId :=
  ⟨filePath.hash.toNat⟩

/-- Analyze a source file and produce a CompiledModule -/
def analyzeSource (filePath : String) (content : String) : CompiledModule := Id.run do
  let moduleName := moduleNameFromPath filePath
  let fileId := fileIdFromPath filePath

  -- Phase 1: Create source file with line information
  let sourceFile := SourceFile.create fileId filePath content

  -- Phase 2: Lexing
  let (tokens, lexDiags) := lexCode sourceFile

  -- Phase 3: Parsing (infallible - always produces CST)
  let (cst, parseDiags) := Parse.parseSourceFile.run' tokens sourceFile

  -- Phase 4: Build symbol table from CST
  let symbols := buildSymbolTable moduleName filePath cst

  -- Phase 5: Lower to AST (optional, may fail with errors)
  let (astOpt, lowerDiags) := lower cst moduleName

  -- Combine all diagnostics
  let allDiags := lexDiags ++ parseDiags ++ lowerDiags

  return {
    name := moduleName
    filePath := filePath
    sourceFile := sourceFile
    cst := cst
    ast := astOpt
    symbols := symbols
    diagnostics := allDiags
  }

/-- Re-analyze a file (same as analyze, but clearer intent) -/
def reanalyzeSource (filePath : String) (content : String) : CompiledModule :=
  analyzeSource filePath content

/-- Check if content has changed significantly (for debouncing) -/
def contentChanged (old new : String) : Bool :=
  old != new

/-- Quick syntax check - just lex and parse, don't build full symbols -/
def quickCheck (filePath : String) (content : String) : Diagnostics := Id.run do
  let fileId := fileIdFromPath filePath
  let sourceFile := SourceFile.create fileId filePath content
  let (tokens, lexDiags) := lexCode sourceFile
  let (cst, parseDiags) := Parse.parseSourceFile.run' tokens sourceFile

  -- Collect CST errors too
  let cstErrors := cst.collectErrors.map fun (span, msg) =>
    Soma.Syntax.Diagnostic.error msg span

  return lexDiags ++ parseDiags ++ cstErrors

/-- Get all error diagnostics -/
def getErrors (mod : CompiledModule) : Diagnostics :=
  mod.diagnostics.filter (·.severity == .error)

/-- Get error count -/
def getErrorCount (mod : CompiledModule) : Nat :=
  getErrors mod |>.size

/-- Check if module has any errors -/
def hasAnyErrors (mod : CompiledModule) : Bool :=
  getErrorCount mod > 0

/-- Create diagnostics from CST error nodes -/
def cstErrorsToDiagnostics (cst : SyntaxNode) : Diagnostics :=
  cst.collectErrors.map fun (span, msg) =>
    Soma.Syntax.Diagnostic.error msg span

/-- Merge diagnostics from multiple sources -/
def mergeDiagnostics (sources : Array Diagnostics) : Diagnostics :=
  sources.foldl (· ++ ·) #[]

/-- Resolve a symbol name to its definition, checking imports -/
def resolveSymbol (name : String) (currentMod : CompiledModule) (allModules : Array CompiledModule)
    : Option DefinitionSite :=
  -- First check current module
  match currentMod.symbols.lookupDefinition name with
  | some def_ => some def_
  | none =>
    -- Check imported modules
    let fromImports := currentMod.symbols.imports.findSome? fun imp =>
      -- Empty items = import all, otherwise check if name is in list
      let shouldCheck := imp.items.isEmpty || imp.items.contains name
      if shouldCheck then
        allModules.findSome? fun mod =>
          if mod.name == imp.modulePath || mod.filePath.endsWith imp.modulePath then
            mod.symbols.lookupDefinition name
          else none
      else none
    match fromImports with
    | some def_ => some def_
    | none =>
      -- Fallback: check all modules
      allModules.findSome? fun mod => mod.symbols.lookupDefinition name

/-- Get all visible symbols at a position (for completion) -/
def visibleSymbols (currentMod : CompiledModule) (allModules : Array CompiledModule)
    : Array DefinitionSite :=
  let localDefs := currentMod.symbols.allDefinitions

  -- Add symbols from imports
  let importedDefs := currentMod.symbols.imports.foldl (init := #[]) fun acc imp =>
    allModules.foldl (init := acc) fun acc2 mod =>
      if mod.name == imp.modulePath || mod.filePath.endsWith imp.modulePath then
        if imp.items.isEmpty then
          -- Import all
          acc2 ++ mod.symbols.allDefinitions
        else
          -- Import specific items
          imp.items.foldl (init := acc2) fun acc3 itemName =>
            match mod.symbols.lookupDefinition itemName with
            | some def_ => acc3.push def_
            | none => acc3
      else acc2

  localDefs ++ importedDefs

/-- Check if a file is a Soma source file -/
def isSomaFile (path : String) : Bool :=
  path.endsWith ".soma"

end Lsp
