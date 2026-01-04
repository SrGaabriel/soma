import Std.Data.HashSet
import Soma.Syntax
import Soma.Metal
import Soma.Metal.Lower.Decl
import Soma.Dependent
import Soma.Dependent.Incremental
import Soma.Project.Check
import Lsp.State
import Lsp.Symbols
import Lsp.Loc

namespace Lsp

open Std

open Soma.Syntax
open Soma.Dependent
open Soma.Dependent.Driver
open Soma.Dependent.Incremental (IncrementalState)
open Soma.Metal (UntypedModule)
open Soma.Metal.Lower (IncrementalLowerResult lowerModuleFresh lowerModuleIncremental getDeclName)
open Soma.Check (moduleNameFromPath fileIdFromPath typeCheckModule)

/-- Extract imported module paths from a symbol table -/
def extractImportedModules (symbols : SymbolTable) : Array String :=
  symbols.imports.map (·.modulePath)

/-- Build declNodeIds mapping from definitions -/
def buildDeclNodeIds (defs : Array CstDefinition) : Std.HashMap NodeId String :=
  defs.foldl (fun acc def_ => acc.insert def_.declId def_.name) {}

/-- Walk up from a node to find its enclosing declaration -/
partial def findEnclosingDecl (tree : RedTree) (node : RedNode) : Option NodeId :=
  if let some kind := node.syntaxKind? then
    if kind.isDecl then some node.id
    else match tree.parent? node with
      | some parent => findEnclosingDecl tree parent
      | none => none
  else match tree.parent? node with
    | some parent => findEnclosingDecl tree parent
    | none => none

/-- Find top-level declaration NodeIds that contain any changed node -/
def findChangedDeclIds (tree : RedTree) (changedIds : HashSet NodeId) : HashSet NodeId :=
  if changedIds.isEmpty then {}
  else
    tree.nodes.foldl (fun acc node =>
      if changedIds.contains node.id then
        match findEnclosingDecl tree node with
        | some declId => acc.insert declId
        | none => acc
      else acc) {}

/-- Analyze a source file from scratch (no prior state) -/
def analyzeSourceFresh (filePath : String) (content : String) : CompiledModule := Id.run do
  let moduleName := moduleNameFromPath filePath
  let fileId := fileIdFromPath filePath

  -- Phase 1: Create source file
  let sourceFile := SourceFile.create fileId filePath content

  -- Phase 2+3: Lex and parse (fresh parse)
  let (parsedTree, frontendDiags) := parseToTree sourceFile

  -- Phase 4: Build symbol table
  let symbols := buildSymbolTable moduleName filePath parsedTree.red
  let cstDefs := collectDefinitions parsedTree.red
  let declNodeIds := buildDeclNodeIds cstDefs

  -- Phase 5: Lower CST to AST
  let (ast, astLowerDiags) := lower parsedTree moduleName

  -- Build declAsts cache for future incremental updates
  let allDeclIds := collectDeclNodeIds parsedTree
  let (declAsts, _) := lowerDeclarationsByIds parsedTree allDeclIds

  -- Phase 6: Lower AST to Metal IR (using incremental infrastructure for caching)
  let metalResult := lowerModuleFresh ast
  let metalLowerDiags := Soma.Metal.Lower.LowerError.toDiagnostics metalResult.errors

  -- Phase 7: Dependent type checking using the shared pipeline
  -- For LSP single-file analysis, we have no dependencies (empty seed globals/instances)
  let (globals, instanceEnv, _instanceMap, incrState, tcErrors) :=
    typeCheckModule metalResult.module moduleName Globals.empty InstanceEnv.empty none

  -- Update incremental state with imported modules
  let importedMods := extractImportedModules symbols
  let finalIncrState := importedMods.foldl (fun acc mod => acc.addImportedModule mod) incrState

  let inferDiags := tcErrorsToDiagnostics tcErrors

  let allDiags := frontendDiags ++ astLowerDiags ++ metalLowerDiags ++ inferDiags

  return {
    name := moduleName
    filePath := filePath
    parsedTree := parsedTree
    ast := some ast
    symbols := symbols
    diagnostics := allDiags
    declNodeIds := declNodeIds
    declAsts := declAsts
    metalResult := some metalResult
    globals := some globals
    instanceEnv := some instanceEnv
    incrementalState := some finalIncrState
  }

/-- Analyze a source file incrementally using prior state -/
def analyzeSourceIncremental (filePath : String) (content : String)
    (oldModule : CompiledModule) : CompiledModule := Id.run do
  let moduleName := moduleNameFromPath filePath
  let fileId := fileIdFromPath filePath

  -- Phase 1: Create source file
  let sourceFile := SourceFile.create fileId filePath content

  -- Phase 2+3: Incremental reparse (preserves NodeIds for unchanged subtrees)
  let (parsedTree, frontendDiags) := reparseToTree oldModule.parsedTree sourceFile

  -- Phase 4: Find which NodeIds changed
  let oldNodeIds := oldModule.parsedTree.red.idToIdx
  let newNodeIds := parsedTree.red.idToIdx

  -- NodeIds in new tree that weren't in old tree = changed/new nodes
  let changedIds : HashSet NodeId :=
    newNodeIds.fold (init := {}) fun acc nodeId _ =>
      if oldNodeIds.contains nodeId then acc
      else acc.insert nodeId

  -- Find which top-level declarations were affected
  let changedDeclIds := findChangedDeclIds parsedTree.red changedIds

  -- Phase 5: Incremental symbol table update
  let (symbols, cstDefs) :=
    if changedDeclIds.isEmpty then
      -- Nothing changed, reuse old symbols
      (oldModule.symbols, collectDefinitions parsedTree.red)
    else
      -- Update only changed definitions
      let newSymbols := updateSymbolTableIncremental
        oldModule.symbols parsedTree.red changedDeclIds moduleName filePath
      (newSymbols, collectDefinitions parsedTree.red)

  let declNodeIds := buildDeclNodeIds cstDefs

  -- Phase 6: Incremental AST lowering
  let (declAsts, astLowerDiags) :=
    if changedDeclIds.isEmpty then
      -- Nothing changed, reuse all cached ASTs
      (oldModule.declAsts, #[])
    else
      -- Lower only the changed declarations
      let (freshAsts, diags) := lowerDeclarationsByIds parsedTree changedDeclIds.toArray
      -- Start with old ASTs, remove changed ones, then merge fresh ones
      let prunedAsts := changedDeclIds.fold (init := oldModule.declAsts) fun acc declId =>
        acc.erase declId
      -- Merge fresh ASTs into the pruned map
      let mergedAsts := freshAsts.fold (init := prunedAsts) fun acc nodeId decl =>
        acc.insert nodeId decl
      (mergedAsts, diags)

  -- Build the Module from the declaration map (in source order)
  let ast := buildModuleFromDeclMap parsedTree declAsts moduleName

  -- Phase 7: Incremental Metal lowering
  let changedDeclNames := changedDeclIds.fold (init := #[]) fun acc nodeId =>
    match oldModule.declNodeIds.get? nodeId with
    | some name => acc.push name
    | none =>
      -- New declaration: find its name from the AST
      match declAsts.get? nodeId with
      | some decl =>
        match getDeclName decl with
        | some name => acc.push name
        | none => acc
      | none => acc

  let metalResult := match oldModule.metalResult with
    | some oldMetal =>
      if changedDeclNames.isEmpty then oldMetal
      else lowerModuleIncremental ast changedDeclNames oldMetal
    | none => lowerModuleFresh ast

  let metalLowerDiags := Soma.Metal.Lower.LowerError.toDiagnostics metalResult.errors

  -- Phase 8: Incremental dependent type checking using the shared pipeline
  -- Get or create previous incremental state
  let prevIncrState := oldModule.incrementalState

  -- Use the shared type checking pipeline with previous state for incremental checking
  let (globals, instanceEnv, _instanceMap, incrState, tcErrors) :=
    typeCheckModule metalResult.module moduleName Globals.empty InstanceEnv.empty prevIncrState

  -- Update incremental state with imported modules
  let importedMods := extractImportedModules symbols
  let finalIncrState := importedMods.foldl (fun acc mod => acc.addImportedModule mod) incrState

  let inferDiags := tcErrorsToDiagnostics tcErrors

  let allDiags := frontendDiags ++ astLowerDiags ++ metalLowerDiags ++ inferDiags

  return {
    name := moduleName
    filePath := filePath
    parsedTree := parsedTree
    ast := some ast
    symbols := symbols
    diagnostics := allDiags
    declNodeIds := declNodeIds
    declAsts := declAsts
    metalResult := some metalResult
    globals := some globals
    instanceEnv := some instanceEnv
    incrementalState := some finalIncrState
  }

/-- Analyze a source file, using incremental analysis if old module is available -/
def analyzeSource (filePath : String) (content : String)
    (oldModule? : Option CompiledModule := none) : CompiledModule :=
  match oldModule? with
  | none => analyzeSourceFresh filePath content
  | some oldModule => analyzeSourceIncremental filePath content oldModule

/-- Get all error diagnostics -/
def getErrors (mod : CompiledModule) : Diagnostics :=
  mod.diagnostics.filter (·.severity == .error)

/-- Get error count -/
def getErrorCount (mod : CompiledModule) : Nat :=
  getErrors mod |>.size

/-- Check if module has any errors -/
def hasAnyErrors (mod : CompiledModule) : Bool :=
  getErrorCount mod > 0

/-- Create diagnostics from red tree error nodes -/
def treeErrorsToDiagnostics (tree : RedTree) : Diagnostics :=
  tree.nodes.filterMap fun node =>
    match node.green with
    | .error msg _ _ => some (Diagnostic.error msg (tree.spanOf node))
    | .missing expected => some (Diagnostic.error s!"expected {expected.describe}" (tree.spanOf node))
    | _ => none

/-- Merge diagnostics from multiple sources -/
def mergeDiagnostics (sources : Array Diagnostics) : Diagnostics :=
  sources.foldl (· ++ ·) #[]

/-- Resolve a symbol name to its definition, checking imports -/
def resolveSymbol (name : String) (currentMod : CompiledModule) (allModules : Array CompiledModule)
    : Option DefinitionSite :=
  match currentMod.symbols.lookupDefinition name with
  | some def_ => some def_
  | none =>
    let fromImports := currentMod.symbols.imports.findSome? fun imp =>
      let shouldCheck := imp.items.isEmpty || imp.items.contains name
      if shouldCheck then
        allModules.findSome? fun mod =>
          if mod.name == imp.modulePath || mod.filePath.endsWith imp.modulePath then
            mod.symbols.lookupDefinition name
          else none
      else none
    match fromImports with
    | some def_ => some def_
    | none => allModules.findSome? fun mod => mod.symbols.lookupDefinition name

/-- Get all visible symbols at a position (for completion) -/
def visibleSymbols (currentMod : CompiledModule) (allModules : Array CompiledModule)
    : Array DefinitionSite :=
  let localDefs := currentMod.symbols.allDefinitions
  let importedDefs := currentMod.symbols.imports.foldl (init := #[]) fun acc imp =>
    allModules.foldl (init := acc) fun acc2 mod =>
      if mod.name == imp.modulePath || mod.filePath.endsWith imp.modulePath then
        if imp.items.isEmpty then
          acc2 ++ mod.symbols.allDefinitions
        else
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
