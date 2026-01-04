import Std.Data.HashMap
import Soma.Syntax
import Soma.Metal.Lower.Decl
import Soma.Dependent.Monad
import Soma.Dependent.Incremental
import Lsp.Cst

namespace Lsp

open Soma.Syntax
open Soma.Metal.Lower (IncrementalLowerResult)
open Soma.Dependent (Globals InstanceEnv)

/-- Symbol kinds for LSP features -/
inductive SymbolKind where
  | function
  | type
  | constructor
  | field
  | trait
  | method
  | variable
  | typeVariable
  | module
  | parameter
  deriving Repr, BEq, Inhabited

instance : ToString SymbolKind where
  toString
    | .function => "function"
    | .type => "type"
    | .constructor => "constructor"
    | .field => "field"
    | .trait => "trait"
    | .method => "method"
    | .variable => "variable"
    | .typeVariable => "type variable"
    | .module => "module"
    | .parameter => "parameter"

/-- Convert SyntaxKind to SymbolKind -/
def syntaxKindToSymbolKind : SyntaxKind → SymbolKind
  | .declDef => .function
  | .declData => .type
  | .declStruct => .type
  | .declTrait => .trait
  | .constructor => .constructor
  | .field => .field
  | .traitMethod => .method
  | .patVar => .variable
  | .typeVar => .typeVariable
  | _ => .variable

/-- A definition site with full CST information -/
structure DefinitionSite where
  /-- Symbol name -/
  name : String
  /-- Symbol kind -/
  kind : SymbolKind
  /-- The name token (for precise location) -/
  nameSpan : Span
  /-- The full declaration span -/
  declSpan : Span
  /-- Type signature as text (if available) -/
  typeSignature : Option String
  /-- Module where defined -/
  moduleName : String
  /-- File path -/
  filePath : String
  deriving Repr, Inhabited

/-- A reference to a symbol -/
structure SymbolReference where
  /-- The referenced name -/
  name : String
  /-- Location of the reference -/
  span : Span
  /-- Context of the reference -/
  context : SyntaxContext
  deriving Repr, Inhabited

/-- Import information -/
structure ImportInfo where
  /-- Module path (e.g., "base/core") -/
  modulePath : String
  /-- Specific items imported (empty = all) -/
  items : Array String
  /-- Span of the import declaration -/
  span : Span
  deriving Repr, Inhabited

/-- Symbol table for a module -/
structure SymbolTable where
  /-- All definitions, indexed by name -/
  definitions : Std.HashMap String DefinitionSite := {}
  /-- All references, indexed by name -/
  references : Std.HashMap String (Array SymbolReference) := {}
  /-- Imports from other modules -/
  imports : Array ImportInfo := #[]
  deriving Inhabited

namespace SymbolTable

/-- Create an empty symbol table -/
def empty : SymbolTable := {}

/-- Add a definition -/
def addDefinition (st : SymbolTable) (def_ : DefinitionSite) : SymbolTable :=
  { st with definitions := st.definitions.insert def_.name def_ }

/-- Add a reference -/
def addReference (st : SymbolTable) (ref : SymbolReference) : SymbolTable :=
  let existing := st.references.getD ref.name #[]
  { st with references := st.references.insert ref.name (existing.push ref) }

/-- Add an import -/
def addImport (st : SymbolTable) (imp : ImportInfo) : SymbolTable :=
  { st with imports := st.imports.push imp }

/-- Look up a definition by name -/
def lookupDefinition (st : SymbolTable) (name : String) : Option DefinitionSite :=
  st.definitions.get? name

/-- Get all definitions as array -/
def allDefinitions (st : SymbolTable) : Array DefinitionSite :=
  st.definitions.toArray.map (·.2)

/-- Get all definition names -/
def allNames (st : SymbolTable) : Array String :=
  st.definitions.toArray.map (·.1)

/-- Get references to a name -/
def getReferences (st : SymbolTable) (name : String) : Array SymbolReference :=
  st.references.getD name #[]

/-- Get definitions of a specific kind -/
def definitionsOfKind (st : SymbolTable) (kind : SymbolKind) : Array DefinitionSite :=
  st.allDefinitions.filter (·.kind == kind)

end SymbolTable

/-- A compiled module with CST, optional AST, and symbol table -/
structure CompiledModule where
  /-- Module name (derived from file) -/
  name : String
  /-- File path -/
  filePath : String
  /-- The parsed tree (green + red with stable NodeIds) -/
  parsedTree : ParsedTree
  /-- Abstract Syntax Tree (present if lowering succeeded) -/
  ast : Option Module := none
  /-- Symbol table built from CST -/
  symbols : SymbolTable := {}
  /-- All diagnostics from all phases -/
  diagnostics : Diagnostics := #[]
  /-- Mapping from declaration NodeId to its name -/
  declNodeIds : Std.HashMap NodeId String := {}
  /-- Cached AST declarations by NodeId -/
  declAsts : Std.HashMap NodeId Decl := {}
  /-- Cached Metal lowering result  -/
  metalResult : Option IncrementalLowerResult := none
  /-- Cached globals environment -/
  globals : Option Globals := none
  /-- Cached instance environment -/
  instanceEnv : Option InstanceEnv := none
  /-- Incremental type checking state (dependency tracking and caching) -/
  incrementalState : Option Soma.Dependent.Incremental.IncrementalState := none
  deriving Inhabited

namespace CompiledModule

/-- Get the red tree (for compatibility) -/
def tree (m : CompiledModule) : RedTree :=
  m.parsedTree.red

/-- Get source file -/
def sourceFile (m : CompiledModule) : SourceFile :=
  m.parsedTree.red.source

/-- Get source content -/
def sourceContent (m : CompiledModule) : String :=
  m.parsedTree.red.source.content

/-- Check if module has errors -/
def hasErrors (m : CompiledModule) : Bool :=
  m.diagnostics.hasErrors || m.parsedTree.red.nodes.any (·.isError)

/-- Get error count -/
def errorCount (m : CompiledModule) : Nat :=
  m.diagnostics.errorCount + (m.parsedTree.red.nodes.filter (·.isError)).size

/-- Look up a symbol by name -/
def lookupSymbol (m : CompiledModule) (name : String) : Option DefinitionSite :=
  m.symbols.lookupDefinition name

/-- Get all symbol names -/
def allSymbolNames (m : CompiledModule) : Array String :=
  m.symbols.allNames

/-- Get completions for this module -/
def getCompletions (m : CompiledModule) : Array DefinitionSite :=
  m.symbols.allDefinitions

/-- Get completions of a specific kind -/
def getCompletionsOfKind (m : CompiledModule) (kind : SymbolKind) : Array DefinitionSite :=
  m.symbols.definitionsOfKind kind

end CompiledModule

/-- LSP server state -/
structure LspState where
  /-- Compiled modules by file path -/
  modules : Std.HashMap String CompiledModule := {}
  /-- Workspace root path -/
  workspaceRoot : Option String := none
  /-- Reverse dependency map: module name → modules that import it -/
  reverseDeps : Std.HashMap String (Std.HashSet String) := {}
  /-- Module name to file path mapping -/
  moduleNameToPath : Std.HashMap String String := {}
  deriving Inhabited

namespace LspState

/-- Get a module by file path -/
def getModule (s : LspState) (filePath : String) : Option CompiledModule :=
  s.modules.get? filePath

/-- Set a module -/
def setModule (s : LspState) (filePath : String) (m : CompiledModule) : LspState :=
  { s with modules := s.modules.insert filePath m }

/-- Remove a module -/
def removeModule (s : LspState) (filePath : String) : LspState :=
  { s with modules := s.modules.erase filePath }

/-- Get all modules -/
def allModules (s : LspState) : Array CompiledModule :=
  s.modules.toArray.map (·.2)

/-- Find a module by name -/
def findModuleByName (s : LspState) (name : String) : Option CompiledModule :=
  s.allModules.find? (·.name == name)

/-- Look up a symbol across all modules -/
def lookupSymbolGlobal (s : LspState) (name : String) : Option (CompiledModule × DefinitionSite) := do
  for mod in s.allModules do
    if let some def_ := mod.lookupSymbol name then
      return (mod, def_)
  none

/-- Get all symbols from all modules -/
def allSymbols (s : LspState) : Array DefinitionSite :=
  s.allModules.foldl (fun acc m => acc ++ m.symbols.allDefinitions) #[]

/-- Register module name to file path mapping -/
def registerModulePath (s : LspState) (moduleName : String) (filePath : String) : LspState :=
  { s with moduleNameToPath := s.moduleNameToPath.insert moduleName filePath }

/-- Get file path for a module name -/
def getModulePath (s : LspState) (moduleName : String) : Option String :=
  s.moduleNameToPath.get? moduleName

/-- Add a reverse dependency: depModule is imported by importerModule -/
def addReverseDep (s : LspState) (depModule : String) (importerModule : String) : LspState :=
  let existing := s.reverseDeps.getD depModule {}
  { s with reverseDeps := s.reverseDeps.insert depModule (existing.insert importerModule) }

/-- Remove all reverse dependencies where importerModule is the importer -/
def clearReverseDepsFor (s : LspState) (importerModule : String) : LspState :=
  let reverseDeps' := s.reverseDeps.fold (init := s.reverseDeps) fun acc depMod importers =>
    acc.insert depMod (importers.erase importerModule)
  { s with reverseDeps := reverseDeps' }

/-- Update reverse dependencies for a module based on its imports -/
def updateReverseDeps (s : LspState) (moduleName : String) (imports : Array String) : LspState :=
  -- First clear old reverse deps for this module
  let s' := s.clearReverseDepsFor moduleName
  -- Then add new ones
  imports.foldl (fun acc imp => acc.addReverseDep imp moduleName) s'

/-- Get all modules that import a given module (direct dependents) -/
def getDirectDependents (s : LspState) (moduleName : String) : Array String :=
  match s.reverseDeps.get? moduleName with
  | some deps => deps.toArray
  | none => #[]

/-- Get all modules that transitively depend on a given module -/
def getTransitiveDependents (s : LspState) (moduleName : String) : Array String := Id.run do
  let mut visited : Std.HashSet String := {}
  let mut result : Array String := #[]
  let mut worklist : Array String := #[moduleName]

  while !worklist.isEmpty do
    let current := worklist[0]!
    worklist := worklist.extract 1 worklist.size

    if visited.contains current then
      continue

    visited := visited.insert current

    -- Don't include the original module in the result
    if current != moduleName then
      result := result.push current

    -- Add direct dependents to worklist
    let dependents := s.getDirectDependents current
    for dep in dependents do
      if !visited.contains dep then
        worklist := worklist.push dep

  return result

end LspState

end Lsp
