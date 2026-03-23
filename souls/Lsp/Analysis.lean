import Std.Data.HashSet
import Soma.Syntax
import Soma.Dependent.Lower
import Soma.Dependent
import Soma.Dependent.Incremental
import Soma.Project.Check
import Lsp.State
import Lsp.Scope
import Lsp.Symbols
import Lsp.Loc

namespace Lsp

open Std

open Soma.Syntax
open Soma.Dependent (Globals InstanceEnv AbbrevEnv)
open Soma.Dependent.Incremental (IncrementalState)
open Soma.Project (SymbolEnv)
open Soma.Project.Check (moduleNameFromPath fileIdFromPath)

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

/-- Extract the declaration name from a syntax Decl -/
private def getDeclName : Decl → Option String
  | .def_ _ name _ _ _ _ => some name.name
  | .inductive _ name _ _ _ _ => some name.name
  | .record _ name _ _ _ _ => some name.name
  | .trait _ name _ _ _ _ => some name.name
  | .abbrev name _ _ _ => some name.name
  | _ => none

/-- Analyze a source file from scratch (no prior state) -/
def analyzeSourceFresh (filePath : String) (content : String)
    (checkedDeps : Std.HashMap String Soma.Project.Check.CheckedModule := {})
    (preludeSymbols : Array String := #[])
    (moduleName? : Option String := none)
    (existingChecked : Option Soma.Project.Check.CheckedModule := none) : CompiledModule := Id.run do
  let moduleName := moduleName?.getD (moduleNameFromPath filePath)
  let fileId := fileIdFromPath filePath

  -- Phase 1: Create source file
  let sourceFile := SourceFile.create fileId filePath content

  -- Phase 2+3: Lex and parse (fresh parse)
  let (parsedTree, frontendDiags) := parseToTree sourceFile

  -- Phase 4: Build symbol table
  let symbols := buildSymbolTable moduleName filePath parsedTree.red
  let cstDefs := collectDefinitions parsedTree.red
  let declNodeIds := buildDeclNodeIds cstDefs

  -- Phase 4b: Build local scope map
  let scopeMap := buildScopeMap parsedTree.red

  -- Phase 5: Lower CST to AST
  let (ast, astLowerDiags) := lower parsedTree moduleName

  -- Build declAsts cache for future incremental updates
  let allDeclIds := collectDeclNodeIds parsedTree
  let (declAsts, _) := lowerDeclarationsByIds parsedTree allDeclIds

  match existingChecked with
  | some cm =>
    return {
      name := moduleName
      filePath := filePath
      parsedTree := parsedTree
      ast := some ast
      symbols := symbols
      diagnostics := frontendDiags ++ astLowerDiags
      declNodeIds := declNodeIds
      declAsts := declAsts
      elabResult := none
      globals := some cm.globals
      instanceEnv := some cm.instanceEnv
      incrementalState := some cm.incrementalState
      scopeMap := scopeMap
    }
  | none =>

  -- Phase 7: Use checkModule from the compiler pipeline for type checking
  let modName := Soma.Project.ModuleName.fromString moduleName
  let modInfo : Soma.Project.ModuleInfo := {
    name := modName
    path := System.FilePath.mk filePath
    content := content
    sourceFile := sourceFile
    ast := ast
  }
  let packageName := modName.package
  let supply := Soma.UniqueSupply.initial moduleName
  let (checkDiags, checkedModule?, _) :=
    Soma.Project.Check.checkModule modInfo checkedDeps
      Globals.empty InstanceEnv.empty AbbrevEnv.empty
      {} packageName supply preludeSymbols

  let globals := checkedModule?.map (·.globals)
  let instanceEnv := checkedModule?.map (·.instanceEnv)
  let incrState := checkedModule?.map (·.incrementalState)

  let allDiags := frontendDiags ++ astLowerDiags ++ checkDiags

  return {
    name := moduleName
    filePath := filePath
    parsedTree := parsedTree
    ast := some ast
    symbols := symbols
    diagnostics := allDiags
    declNodeIds := declNodeIds
    declAsts := declAsts
    elabResult := none
    globals := globals
    instanceEnv := instanceEnv
    incrementalState := incrState
    scopeMap := scopeMap
  }

/-- Analyze a source file incrementally using prior state -/
def analyzeSourceIncremental (filePath : String) (content : String)
    (oldModule : CompiledModule)
    (checkedDeps : Std.HashMap String Soma.Project.Check.CheckedModule := {})
    (preludeSymbols : Array String := #[])
    (moduleName? : Option String := none) : CompiledModule := Id.run do
  let moduleName := moduleName?.getD (moduleNameFromPath filePath)
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
      (oldModule.symbols, collectDefinitions parsedTree.red)
    else
      let newSymbols := updateSymbolTableIncremental
        oldModule.symbols parsedTree.red changedDeclIds moduleName filePath
      (newSymbols, collectDefinitions parsedTree.red)

  let declNodeIds := buildDeclNodeIds cstDefs

  -- Build local scope map
  let scopeMap := buildScopeMap parsedTree.red

  -- Phase 6: Incremental AST lowering
  let (declAsts, astLowerDiags) :=
    if changedDeclIds.isEmpty then
      (oldModule.declAsts, #[])
    else
      let (freshAsts, diags) := lowerDeclarationsByIds parsedTree changedDeclIds.toArray
      let prunedAsts := changedDeclIds.fold (init := oldModule.declAsts) fun acc declId =>
        acc.erase declId
      let mergedAsts := freshAsts.fold (init := prunedAsts) fun acc nodeId decl =>
        acc.insert nodeId decl
      (mergedAsts, diags)

  -- Build the Module from the declaration map (in source order)
  let ast := buildModuleFromDeclMap parsedTree declAsts moduleName

  -- Phase 7: Use checkModule from the compiler pipeline for type checking
  let modName := Soma.Project.ModuleName.fromString moduleName
  let modInfo : Soma.Project.ModuleInfo := {
    name := modName
    path := System.FilePath.mk filePath
    content := content
    sourceFile := sourceFile
    ast := ast
  }
  let packageName := modName.package
  let supply := Soma.UniqueSupply.initial moduleName
  let (checkDiags, _checkedModule, _) :=
    Soma.Project.Check.checkModule modInfo checkedDeps
      Globals.empty InstanceEnv.empty AbbrevEnv.empty
      {} packageName supply preludeSymbols

  let globals := _checkedModule.map (·.globals)
  let instanceEnv := _checkedModule.map (·.instanceEnv)
  let incrState := _checkedModule.map (·.incrementalState)

  let allDiags := frontendDiags ++ astLowerDiags ++ checkDiags

  return {
    name := moduleName
    filePath := filePath
    parsedTree := parsedTree
    ast := some ast
    symbols := symbols
    diagnostics := allDiags
    declNodeIds := declNodeIds
    declAsts := declAsts
    elabResult := none
    globals := globals
    instanceEnv := instanceEnv
    incrementalState := incrState
    scopeMap := scopeMap
  }

/-- Analyze a source file, using incremental analysis if old module is available -/
def analyzeSource (filePath : String) (content : String)
    (oldModule? : Option CompiledModule := none)
    (checkedDeps : Std.HashMap String Soma.Project.Check.CheckedModule := {})
    (preludeSymbols : Array String := #[])
    (moduleName? : Option String := none)
    (existingChecked : Option Soma.Project.Check.CheckedModule := none) : CompiledModule :=
  match oldModule? with
  | none => analyzeSourceFresh filePath content checkedDeps preludeSymbols moduleName? existingChecked
  | some oldModule => analyzeSourceIncremental filePath content oldModule checkedDeps preludeSymbols moduleName?

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
