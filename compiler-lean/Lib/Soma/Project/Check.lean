import Std.Data.HashSet
import Soma.Syntax
import Soma.Metal
import Soma.Metal.Lower.Decl
import Soma.Infer
import Soma.Unique
import Soma.Project.Module
import Soma.Project.Graph
import Soma.Project.Symbol

namespace Soma.Check

open Std (HashSet)
open Soma.Syntax
open Soma.Metal.Lower (IncrementalLowerResult lowerModuleFresh lowerModuleWithExternals lowerModuleIncremental GlobalEnv)
open Soma.Infer
open Soma.Typing
open Soma.Project
open Soma (UniqueSupply)
open Soma.Infer.Gen (applyTypeArgs)

/-! ## Helper functions -/

/-- Derive module name from file path -/
def moduleNameFromPath (filePath : String) : String :=
  let parts := filePath.splitOn "/"
  let fileName := parts.getLast!
  let nameParts := fileName.splitOn "."
  if nameParts.isEmpty then fileName else nameParts.head!

/-- Create a file ID from path -/
def fileIdFromPath (filePath : String) : FileId :=
  ⟨filePath.hash.toNat⟩

/-! ## Phase Results

Each phase returns its output plus diagnostics. We use a simple pattern:
the result is always produced (phases are infallible), diagnostics are collected.
-/

/-- Result of parsing -/
structure ParseResult where
  sourceFile : SourceFile
  tree : ParsedTree
  diagnostics : Diagnostics

/-- Result of CST → AST lowering -/
structure LowerResult where
  ast : Syntax.Module
  diagnostics : Diagnostics

/-- Result of AST → Metal IR lowering -/
structure MetalResult where
  module : Metal.UntypedModule
  result : IncrementalLowerResult  -- Contains caches for incremental updates
  diagnostics : Diagnostics

/-- Result of type inference -/
structure InferResult where
  module : Metal.Module
  typeEnv : TypeEnv
  instanceEnv : InstanceEnv
  diagnostics : Diagnostics

/-- Phase 1+2: Parse source code (lex + parse combined) -/
def parse (filePath : String) (content : String) : ParseResult :=
  let sourceFile := SourceFile.create (fileIdFromPath filePath) filePath content
  let (tree, diags) := parseToTree sourceFile
  { sourceFile, tree, diagnostics := diags }

/-- Phase 2b: Incremental reparse -/
def reparse (oldTree : ParsedTree) (filePath : String) (content : String)
    : ParseResult × HashSet NodeId :=
  let sourceFile := SourceFile.create (fileIdFromPath filePath) filePath content
  let (tree, diags) := reparseToTree oldTree sourceFile
  let oldIds := oldTree.red.idToIdx
  let newIds := tree.red.idToIdx
  let changedIds := newIds.fold (init := {}) fun acc nodeId _ =>
    if oldIds.contains nodeId then acc else acc.insert nodeId
  ({ sourceFile, tree, diagnostics := diags }, changedIds)

/-- Phase 3: Lower CST to AST -/
def lower (tree : ParsedTree) (moduleName : String) : LowerResult :=
  let (ast, diags) := Syntax.lower tree moduleName
  { ast, diagnostics := diags }

/-- Phase 4: Lower AST to Metal IR -/
def metal (ast : Syntax.Module) : MetalResult :=
  let result := lowerModuleFresh ast
  let diags := Metal.Lower.LowerError.toDiagnostics result.errors
  { module := result.module, result, diagnostics := diags }

/-- Phase 4 with external symbols: Lower AST to Metal IR with pre-populated GlobalEnv -/
def metalWithExternals (ast : Syntax.Module) (initialEnv : Metal.Lower.GlobalEnv) : MetalResult :=
  let result := lowerModuleWithExternals ast initialEnv
  let diags := Metal.Lower.LowerError.toDiagnostics result.errors
  { module := result.module, result, diagnostics := diags }

/-- Phase 4b: Incremental Metal lowering -/
def metalIncremental (ast : Syntax.Module) (changedNames : Array String)
    (oldResult : IncrementalLowerResult) : MetalResult :=
  let result := lowerModuleIncremental ast changedNames oldResult
  let diags := Metal.Lower.LowerError.toDiagnostics result.errors
  { module := result.module, result, diagnostics := diags }

/-- Phase 5: Type inference -/
def infer (module : Metal.UntypedModule) (typeEnv : TypeEnv) (instanceEnv : InstanceEnv)
    : InferResult :=
  let ctx : InferContext := { typeEnv, instanceEnv, currentFunction := none }
  let result := inferModule module ctx
  let diags := InferErrors.toDiagnostics result.errors
  { module := result.module, typeEnv, instanceEnv, diagnostics := diags }

/-- Build type environment from a Metal module -/
def buildTypeEnv (module : Metal.UntypedModule)
    (supply : UniqueSupply)
    (externalFns : Array (String × FunctionInfo) := #[])
    (externalTypes : Array (String × Infer.TypeInfo) := #[])
    (externalConstructors : Array (String × Infer.ConstructorInfo) := #[])
    : TypeEnv × UniqueSupply :=
  buildTypeEnvFromModule module externalFns supply externalTypes externalConstructors

/-- Build instance environment from a Metal module -/
def buildInstanceEnv (module : Metal.UntypedModule)
    (externalInstances : InstanceEnv := InstanceEnv.empty)
    (typeEnv : TypeEnv) : InstanceEnv :=
  buildInstanceEnvFromModule module externalInstances typeEnv

/-- Configuration for the full pipeline -/
structure Config where
  /-- External functions from dependencies -/
  externalFunctions : Array (String × FunctionInfo) := #[]
  /-- External instances from dependencies -/
  externalInstances : InstanceEnv := InstanceEnv.empty
  /-- Unique supply for fresh names -/
  supply : UniqueSupply
  /-- Whether to stop after frontend errors -/
  stopOnFrontendErrors : Bool := false

/-- Full pipeline result -/
structure FullResult where
  moduleName : String
  sourceFile : SourceFile
  parsedTree : ParsedTree
  ast : Syntax.Module
  metalModule : Metal.UntypedModule
  metalResult : IncrementalLowerResult
  typedModule : Metal.Module
  typeEnv : TypeEnv
  instanceEnv : InstanceEnv
  diagnostics : Diagnostics

namespace FullResult

def hasErrors (r : FullResult) : Bool := r.diagnostics.hasErrors
def errorCount (r : FullResult) : Nat := r.diagnostics.filter (·.severity == .error) |>.size

end FullResult

/-- Run the full pipeline: parse → lower → metal → infer -/
def full (filePath : String) (content : String) (config : Config) : FullResult := Id.run do
  let moduleName := moduleNameFromPath filePath

  -- Parse
  let parseRes := parse filePath content

  -- Lower CST → AST
  let lowerRes := lower parseRes.tree moduleName
  let frontendDiags := parseRes.diagnostics ++ lowerRes.diagnostics

  -- Metal lowering
  let metalRes := metal lowerRes.ast

  -- Check for early exit on frontend errors
  if config.stopOnFrontendErrors && frontendDiags.hasErrors then
    let (typeEnv, _) := buildTypeEnv metalRes.module config.supply config.externalFunctions
    let instanceEnv := buildInstanceEnv metalRes.module config.externalInstances typeEnv
    return {
      moduleName, sourceFile := parseRes.sourceFile, parsedTree := parseRes.tree
      ast := lowerRes.ast
      metalModule := metalRes.module, metalResult := metalRes.result
      typedModule := { name := moduleName, functions := #[], types := #[], typeClasses := #[], instances := #[] }
      typeEnv, instanceEnv
      diagnostics := frontendDiags ++ metalRes.diagnostics
    }

  -- Build environments
  let (typeEnv, _) := buildTypeEnv metalRes.module config.supply config.externalFunctions
  let instanceEnv := buildInstanceEnv metalRes.module config.externalInstances typeEnv

  -- Type inference
  let inferRes := infer metalRes.module typeEnv instanceEnv

  let allDiags := frontendDiags ++ metalRes.diagnostics ++ inferRes.diagnostics

  return {
    moduleName, sourceFile := parseRes.sourceFile, parsedTree := parseRes.tree
    ast := lowerRes.ast
    metalModule := metalRes.module, metalResult := metalRes.result
    typedModule := inferRes.module
    typeEnv := inferRes.typeEnv, instanceEnv := inferRes.instanceEnv
    diagnostics := allDiags
  }

/-- Simple full pipeline with default config -/
def fullSimple (filePath : String) (content : String) : FullResult :=
  let moduleName := moduleNameFromPath filePath
  full filePath content { supply := UniqueSupply.initial moduleName }

/-- Run full pipeline from file -/
def fullFromFile (filePath : String) (config : Config) : IO FullResult := do
  let content ← IO.FS.readFile filePath
  pure (full filePath content config)

/-- Simple full pipeline from file -/
def fullFromFileSimple (filePath : String) : IO FullResult := do
  let content ← IO.FS.readFile filePath
  pure (fullSimple filePath content)

/-- Parse only -/
def parseOnly (filePath : String) (content : String) : ParseResult :=
  parse filePath content

/-- Parse + lower to AST -/
def toAst (filePath : String) (content : String) (moduleName : Option String := none) : ParseResult × LowerResult :=
  let parseRes := parse filePath content
  let modName := moduleName.getD (moduleNameFromPath filePath)
  let lowerRes := lower parseRes.tree modName
  (parseRes, lowerRes)

/-- Parse + lower to Metal IR -/
def toMetal (filePath : String) (content : String) : ParseResult × LowerResult × MetalResult :=
  let (parseRes, lowerRes) := toAst filePath content
  let metalRes := metal lowerRes.ast
  (parseRes, lowerRes, metalRes)

/-- Check if diagnostics have errors -/
def hasErrors (diags : Diagnostics) : Bool := diags.hasErrors

/-- Combine diagnostics from multiple sources -/
def combineDiags (sources : Array Diagnostics) : Diagnostics :=
  sources.foldl (· ++ ·) #[]

/-- Errors that can occur during project checking -/
inductive CheckError where
  | parseError (module : String) (message : String)
  | typeError (module : String) (errors : Array String)
  | cyclicDependency (modules : Array String)
  | dependencyNotFound (name : String) (path : String)
  | dependencyLoadError (name : String) (message : String)
  deriving Repr

instance : ToString CheckError where
  toString
    | .parseError m msg => s!"Parse error in {m}: {msg}"
    | .typeError m errs => s!"Type errors in {m}:\n" ++ String.intercalate "\n" errs.toList
    | .cyclicDependency mods => s!"Cyclic dependency: {mods.toList}"
    | .dependencyNotFound name path => s!"Dependency '{name}' not found at {path}"
    | .dependencyLoadError name msg => s!"Failed to load dependency '{name}': {msg}"

/-- A fully checked module with typed IR and public exports -/
structure CheckedModule where
  /-- Module name -/
  name : String
  /-- Resolved AST after parsing and lowering -/
  resolvedAst : Syntax.Module
  /-- Typed Metal IR -/
  typedModule : Metal.Module
  /-- Public symbols exported by this module -/
  publicSymbols : SymbolEnv
  /-- Public type class instances exported by this module -/
  publicInstances : Project.InstanceMetadata

namespace CheckedModule

/-- Extract constructor metadata from this module -/
def constructorMetadata (_m : CheckedModule) : Std.HashMap Metal.Name Nat :=
  {}  -- TODO: Extract from typedModule.types when implemented

end CheckedModule

/-- External dependency loaded from metadata JSON -/
structure ExternalDependency where
  /-- Dependency name -/
  name : String
  /-- Metadata version -/
  version : Option String := none
  /-- Symbols by module name -/
  symbols : Std.HashMap String SymbolEnv
  /-- Instances by module name -/
  instances : Std.HashMap String Project.InstanceMetadata
  /-- Constructor tags by name -/
  constructors : Std.HashMap String Nat

/-- Configuration for project checking -/
structure ProjectConfig where
  /-- Root input path (file or directory) -/
  input : System.FilePath
  /-- Optional package/module name override -/
  name : Option String := none
  /-- External dependency paths: (name, path to .meta.json) -/
  deps : Array (String × System.FilePath) := #[]

/-- Result of project checking (type-checking phase) -/
structure ProjectResult where
  /-- Whether checking succeeded without errors -/
  success : Bool
  /-- All diagnostics (errors and warnings) -/
  diagnostics : Diagnostics
  /-- Name of the package/module -/
  packageName : String
  /-- Checked modules in dependency order -/
  checkedModules : Array CheckedModule
  /-- Aggregated public symbols from all modules -/
  symbols : SymbolEnv
  /-- Aggregated public instances from all modules -/
  instances : Project.InstanceMetadata
  /-- Constructor metadata (name → tag) -/
  constructors : Std.HashMap Metal.Name Nat
  /-- Source file map for resolving diagnostic spans -/
  sourceFiles : SourceFileMap

namespace ProjectResult

def failed (name : String) (diags : Diagnostics) (sourceFiles : SourceFileMap := SourceFileMap.empty) : ProjectResult :=
  { success := false, diagnostics := diags, packageName := name,
    checkedModules := #[], symbols := {}, instances := {}, constructors := {}, sourceFiles }

def succeeded (name : String) (diags : Diagnostics) (modules : Array CheckedModule)
    (symbols : SymbolEnv) (instances : Project.InstanceMetadata)
    (constructors : Std.HashMap Metal.Name Nat) (sourceFiles : SourceFileMap) : ProjectResult :=
  { success := true, diagnostics := diags, packageName := name,
    checkedModules := modules, symbols, instances, constructors, sourceFiles }

end ProjectResult

/-- Merge two instance environments -/
def mergeInstanceEnvs (e1 e2 : Project.InstanceMetadata) : Project.InstanceMetadata :=
  e2.fold (init := e1) fun acc className instances =>
    match acc.get? className with
    | none => acc.insert className instances
    | some existing => acc.insert className (existing ++ instances)

/-- Convert Project.InstanceMetadata to Infer.InstanceEnv -/
def projectToInferInstanceEnv (projEnv : InstanceMetadata) : Infer.InstanceEnv :=
  projEnv.fold (init := InstanceEnv.empty) fun acc className instances =>
    instances.foldl (fun env (typeArgs, sym) =>
      let classTyCon := TyCon.mkUser sym.module className sym.unique.id
      let instDecl : Infer.InstanceDecl := {
        className := classTyCon
        args := typeArgs
        typeVars := #[]
        constraints := #[]
        id := env.nextId
        span := sym.span
      }
      env.addInstance instDecl
    ) acc

/-- Convert SymbolEnv to array of function info for type environment building -/
def symbolEnvToFunctionInfos (seed : SymbolEnv) : Array (String × Infer.FunctionInfo) :=
  seed.fold (init := #[]) fun acc sym qt =>
    let metalName : Metal.Name := .user { id := sym.unique.id, module := sym.unique.module, original := sym.name }
    acc.push (sym.name, { qualType := qt, metalName := metalName })

/-- Convert SymbolEnv to array of type info for type environment building -/
def symbolEnvToTypeInfos (seed : SymbolEnv) : Array (String × Infer.TypeInfo) :=
  seed.fold (init := #[]) fun acc sym qt =>
    match sym.kind with
    | .type =>
      let unique : Unique := { id := sym.unique.id, module := sym.unique.module, original := sym.name }
      -- Compute kind from number of type parameters
      let kind := Kind.nary qt.vars.size
      let typeId : TypeId := TypeId.fromUnique unique kind
      let typeInfo : Infer.TypeInfo := {
        typeId := typeId
        params := qt.vars
        constructors := {} -- Constructors are added separately
      }
      acc.push (sym.name, typeInfo)
    | _ => acc

/-- Extract field types from a constructor type -/
private def extractFieldTypes (ty : MonoTy) : Array MonoTy :=
  match ty with
  | .arrow argTy resTy => #[argTy] ++ extractFieldTypes resTy
  | _ => #[]

/-- Convert SymbolEnv to array of constructor info for type environment building -/
def symbolEnvToConstructorInfos (seed : SymbolEnv) : Array (String × Infer.ConstructorInfo) :=
  -- First, build a map from type names to their TypeIds (with correct kinds)
  let typeMap : Std.HashMap String TypeId := seed.fold (init := {}) fun acc sym qt =>
    match sym.kind with
    | .type =>
      let unique : Unique := { id := sym.unique.id, module := sym.unique.module, original := sym.name }
      -- Compute kind from number of type parameters
      let kind := Kind.nary qt.vars.size
      let typeId : TypeId := TypeId.fromUnique unique kind
      acc.insert sym.name typeId
    | _ => acc
  -- Now extract constructors with correct parent TypeIds
  seed.fold (init := #[]) fun acc sym qt =>
    match sym.kind with
    | .dataCon parentType tag =>
      match typeMap.get? parentType with
      | some parentTypeId =>
        let fieldTypes := extractFieldTypes qt.body
        let ctorInfo : Infer.ConstructorInfo := {
          typeName := parentType
          typeId := parentTypeId
          typeParams := qt.vars
          fieldTypes := fieldTypes
          tag := tag
        }
        acc.push (sym.name, ctorInfo)
      | none => acc 
    | _ => acc

/-- Convert SymbolEnv to Metal.Lower.GlobalEnv for pre-populating external symbols -/
def symbolEnvToGlobalEnv (moduleName : String) (seed : SymbolEnv) : Metal.Lower.GlobalEnv :=
  seed.fold (init := Metal.Lower.GlobalEnv.empty moduleName) fun acc sym qt =>
    let unique : Unique := { id := sym.unique.id, module := sym.unique.module, original := sym.name }
    let metalName : Metal.Name := .user unique
    match sym.kind with
    | .type =>
      -- Register as a type
      let typeId : TypeId := TypeId.fromUnique unique
      let tyCon := TyCon.user typeId
      let typeInfo : Metal.Lower.TypeInfo := {
        tyCon := tyCon
        params := qt.vars
        kind := Kind.nary qt.vars.size
        unique := unique
      }
      acc.addType sym.name typeInfo
    | .dataCon parentType tag =>
      -- Register as both a constructor and a global (for value-level usage)
      let ctorInfo : Metal.Lower.ConstructorInfo := {
        name := metalName
        parentType := parentType
        parentUnique := unique -- important: this is the ctor's unique, not parent's
        tag := tag
        fields := #[]  -- Field types aren't needed for name resolution
        span := sym.span
      }
      let globalInfo : Metal.Lower.GlobalInfo := {
        name := metalName
        typeSyntax := none
        definedAt := sym.span
      }
      acc.addConstructor sym.name ctorInfo |>.addGlobal sym.name globalInfo
    | _ =>
      -- Register as a global for value-level usage
      let globalInfo : Metal.Lower.GlobalInfo := {
        name := metalName
        typeSyntax := none
        definedAt := sym.span
      }
      acc.addGlobal sym.name globalInfo

/-- Extract public symbols from a typed module -/
def extractPublicSymbols
    (m : Metal.Module)
    (globalEnv : Metal.Lower.GlobalEnv)
    (packageName : String)
    (seed : SymbolEnv)
    (supply : UniqueSupply)
    : SymbolEnv × UniqueSupply := Id.run do
  let mut acc := seed
  let mut sup := supply
  for fn in m.functions do
    -- Get unique from function name, or generate fresh one
    let (unique, sup') := match fn.name.baseUnique? with
      | some u => (u, sup)
      | none => sup.fresh fn.name.display
    sup := sup'
    -- Get span from globalEnv if available
    let span := match globalEnv.lookupGlobal fn.name.display with
      | some info => info.definedAt
      | none => Span.uninhabited  -- Only for synthetic functions not in globalEnv
    let sym : Symbol := {
      unique := unique
      name := fn.name.display
      kind := .binding
      module := m.name
      package := packageName
      span := span
    }
    acc := acc.insert sym fn.qualifiedType
  -- Extract type class method signatures
  for tc in m.typeClasses do
    let className := tc.name.display
    for (methodName, methodType) in tc.methods do
      let (unique, sup') := match methodName.baseUnique? with
        | some u => (u, sup)
        | none => sup.fresh methodName.display
      sup := sup'
      let span := match globalEnv.lookupGlobal methodName.display with
        | some info => info.definedAt
        | none => Span.uninhabited
      let sym : Symbol := {
        unique := unique
        name := methodName.display
        kind := .typeClassMethod className
        module := m.name
        package := packageName
        span := span
      }
      acc := acc.insert sym methodType
  -- Extract type definitions and their constructors
  for td in m.types do
    let typeName := td.name.display
    let typeVars := td.typeVars
    let (typeUnique, sup') := match td.name.baseUnique? with
      | some u => (u, sup)
      | none => sup.fresh typeName
    sup := sup'
    let typeSym : Symbol := {
      unique := typeUnique
      name := typeName
      kind := .type
      module := m.name
      package := packageName
      span := Span.uninhabited
    }
    let typeQualType : QualifiedType := { vars := typeVars, constraints := #[], body := Ty.unit }
    acc := acc.insert typeSym typeQualType
    -- Export data constructors
    for ctor in td.constructors do
      let (ctorName, ctorTag) := match ctor.name with
        | .ctor _ c tag => (c, tag)
        | n => (n.display, 0)
      -- Each constructor needs its own unique (not the parent type's unique)
      let (ctorUnique, sup') := sup.fresh ctorName
      sup := sup'
      let typeKind := Kind.nary typeVars.size
      let typeId : TypeId := TypeId.fromUnique typeUnique typeKind
      let baseTyCon : Ty typeKind := Ty.userCon typeKind typeId
      let tyVarArgs : Array MonoTy := typeVars.map (fun v => Ty.var v)
      let resultTy : MonoTy := applyTypeArgs baseTyCon tyVarArgs
      let ctorTy := ctor.fields.foldr (fun fieldTy acc => Ty.arrow fieldTy acc) resultTy
      let qualCtorTy : QualifiedType := { vars := typeVars, constraints := #[], body := ctorTy }
      let ctorSym : Symbol := {
        unique := ctorUnique
        name := ctorName
        kind := .dataCon typeName ctorTag
        module := m.name
        package := packageName
        span := Span.uninhabited
      }
      acc := acc.insert ctorSym qualCtorTy
  pure (acc, sup)

/-- Extract public instances from a typed module -/
def extractPublicInstances
    (m : Metal.Module)
    (packageName : String)
    (seed : Project.InstanceMetadata)
    (supply : UniqueSupply)
    : Project.InstanceMetadata × UniqueSupply := Id.run do
  let mut acc := seed
  let mut sup := supply
  for inst in m.instances do
    let instanceName := s!"{inst.className}${inst.instanceType}"
    let (unique, sup') := sup.fresh instanceName
    sup := sup'
    let sym : Symbol := {
      unique := unique
      name := inst.className
      kind := .instanceMethod inst.className inst.className
      module := m.name
      package := packageName
      span := inst.span
    }
    match acc.get? inst.className with
    | none => acc := acc.insert inst.className #[(#[inst.instanceType], sym)]
    | some existing => acc := acc.insert inst.className (existing.push (#[inst.instanceType], sym))
  pure (acc, sup)

/-- Process external dependencies into lookup tables -/
def processExternalDependencies (deps : Array ExternalDependency)
    : Std.HashMap String SymbolEnv × Std.HashMap String Project.InstanceMetadata × Std.HashMap String Nat :=
  deps.foldl (init := ({}, {}, {})) fun (symbols, instances, constructors) dep =>
    let symbols' := dep.symbols.fold (init := symbols) fun acc modName env =>
      acc.insert modName env
    let instances' := dep.instances.fold (init := instances) fun acc modName env =>
      acc.insert modName env
    let constructors' := dep.constructors.fold (init := constructors) fun acc ctorName tag =>
      acc.insert ctorName tag
    (symbols', instances', constructors')

/-- Extract prelude symbols from external dependencies -/
def extractPreludeSymbols (extSymbols : Std.HashMap String SymbolEnv) : Array String :=
  match extSymbols.get? preludeModuleName with
  | none => #[]
  | some env => env.toArray.map fun (sym, _) => sym.name

/-- Check a single module with access to already-checked dependencies -/
def checkModule
    (info : ModuleInfo)
    (checkedDeps : Std.HashMap String CheckedModule)
    (externalSymbols : Std.HashMap String SymbolEnv)
    (externalInstances : Std.HashMap String Project.InstanceMetadata)
    (packageName : String)
    (supply : UniqueSupply)
    : Diagnostics × CheckedModule × UniqueSupply :=
  let modName := info.name.toString

  -- Collect seed environment from checked dependencies
  let seedEnv : SymbolEnv := checkedDeps.fold (init := {}) fun acc _ dep =>
    dep.publicSymbols.fold (init := acc) fun env sym ty => env.insert sym ty

  let seedEnv := externalSymbols.fold (init := seedEnv) fun acc _ env =>
    env.fold (init := acc) fun e sym ty => e.insert sym ty

  let seedInstances : Project.InstanceMetadata := checkedDeps.fold (init := {}) fun acc _ dep =>
    mergeInstanceEnvs acc dep.publicInstances

  let seedInstances := externalInstances.fold (init := seedInstances) fun acc _ env =>
    mergeInstanceEnvs acc env

  -- Convert seed symbols to GlobalEnv for Metal lowering
  let initialGlobalEnv := symbolEnvToGlobalEnv modName seedEnv

  -- Metal lowering with external symbols pre-populated
  let metalRes := metalWithExternals info.ast initialGlobalEnv

  -- Build environments with external dependencies
  let externalFunctions := symbolEnvToFunctionInfos seedEnv
  let externalTypes := symbolEnvToTypeInfos seedEnv
  let externalConstructors := symbolEnvToConstructorInfos seedEnv
  let (typeEnv, supply) := buildTypeEnv metalRes.module supply externalFunctions externalTypes externalConstructors
  let inferInstanceEnv := buildInstanceEnv metalRes.module (projectToInferInstanceEnv seedInstances) typeEnv

  -- Type inference
  let inferRes := infer metalRes.module typeEnv inferInstanceEnv

  let allDiags := metalRes.diagnostics ++ inferRes.diagnostics

  let (publicSymbols, supply) := extractPublicSymbols inferRes.module metalRes.result.globalEnv packageName seedEnv supply
  let (publicInstances, supply) := extractPublicInstances inferRes.module packageName seedInstances supply

  let checkedModule : CheckedModule := {
    name := modName
    resolvedAst := info.ast
    typedModule := inferRes.module
    publicSymbols := publicSymbols
    publicInstances := publicInstances
  }

  (allDiags, checkedModule, supply)

/-- Check all modules in topological order -/
def checkModulesInOrder
    (sortedNames : Array String)
    (graph : ModuleGraph)
    (externalSymbols : Std.HashMap String SymbolEnv)
    (externalInstances : Std.HashMap String Project.InstanceMetadata)
    (packageName : String)
    (supply : UniqueSupply)
    : Diagnostics × Array CheckedModule × UniqueSupply :=
  let (allDiags, _, results, finalSupply) := sortedNames.foldl
    (init := (#[], ({} : Std.HashMap String CheckedModule), #[], supply))
    fun (diags, checked, results, sup) modName =>
      match graph.get? modName with
      | none => (diags, checked, results, sup)
      | some info =>
        let (moduleDiags, cm, sup') := checkModule info checked externalSymbols externalInstances packageName sup
        (diags ++ moduleDiags, checked.insert modName cm, results.push cm, sup')
  (allDiags, results, finalSupply)

/-- Parse a single source file into a ModuleInfo -/
def parseModuleFile (moduleName : String) (path : System.FilePath) : IO (Except Diagnostics ModuleInfo) := do
  let content ← IO.FS.readFile path
  let (parseRes, lowerRes) := toAst path.toString content (some moduleName)
  let allDiags := parseRes.diagnostics ++ lowerRes.diagnostics

  if allDiags.hasErrors then
    pure (.error allDiags)
  else
    let modName := ModuleName.fromString moduleName
    pure (.ok {
      name := modName
      path := path
      content := content
      sourceFile := parseRes.sourceFile
      ast := lowerRes.ast
      contentHash := some (hash content)
    })

/-- Parse all modules in a list, collecting errors -/
def parseModuleFiles (modules : Array (String × System.FilePath)) : IO (Diagnostics × ModuleGraph × SourceFileMap) := do
  let mut graph : ModuleGraph := {}
  let mut sourceMap : SourceFileMap := SourceFileMap.empty
  let mut allDiags : Diagnostics := #[]

  for (name, path) in modules do
    match ← parseModuleFile name path with
    | .ok info =>
      graph := graph.insert name info
      sourceMap := sourceMap.insert info.sourceFile
    | .error diags => allDiags := allDiags ++ diags

  pure (allDiags, graph, sourceMap)

/-- Check a single .soma file -/
def checkSingleFile
    (config : ProjectConfig)
    (loadDeps : Array (String × System.FilePath) → IO (Except CheckError (Array ExternalDependency)))
    : IO ProjectResult := do
  let path := config.input
  let name := config.name.getD (path.fileStem.getD "Main")

  match ← parseModuleFile name path with
  | .error diags =>
    pure (ProjectResult.failed name diags)

  | .ok info =>
    let sourceMap := SourceFileMap.fromSingle info.sourceFile
    let graph : ModuleGraph := ({} : ModuleGraph).insert name info
    let depGraph := buildDependencyGraph graph

    match topoSortModules depGraph with
    | .cycles cyclicDeps =>
      let diags := cyclicDeps.filterMap fun cycle =>
        cycle.imports[0]?.map fun edge =>
          let msg := s!"Cyclic import detected: {cycle.modules.toList}"
          Diagnostic.error msg edge.importSpan
      pure (ProjectResult.failed name diags sourceMap)

    | .sorted sortedNames =>
      match ← loadDeps config.deps with
      | .error e =>
        pure (ProjectResult.failed name #[Diagnostic.error (toString e) Span.uninhabited] sourceMap)

      | .ok deps =>
        let (extSymbols, extInstances, extConstructors) := processExternalDependencies deps
        let supply := UniqueSupply.initial name

        let (checkDiags, checkedModules, _) := checkModulesInOrder
          sortedNames graph extSymbols extInstances name supply

        let symbols := checkedModules.foldl (init := {}) fun acc m =>
          m.publicSymbols.fold (init := acc) fun env sym qt => env.insert sym qt
        let instances := checkedModules.foldl (init := {}) fun acc m =>
          mergeInstanceEnvs acc m.publicInstances
        let constructors := checkedModules.foldl (init := {}) fun acc m =>
          m.constructorMetadata.fold (init := acc) fun env n tag => env.insert n tag

        if checkDiags.hasErrors then
          pure (ProjectResult.failed name checkDiags sourceMap)
        else
          pure (ProjectResult.succeeded name checkDiags checkedModules symbols instances constructors sourceMap)

/-- Check a project directory -/
def checkDirectory
    (config : ProjectConfig)
    (loadDeps : Array (String × System.FilePath) → IO (Except CheckError (Array ExternalDependency)))
    : IO ProjectResult := do
  let rootDir := config.input
  let packageName := config.name.getD (rootDir.fileName.getD "app")

  let modules ← findModules packageName rootDir

  let (parseDiags, graph, sourceMap) ← parseModuleFiles modules

  if parseDiags.hasErrors then
    pure (ProjectResult.failed packageName parseDiags sourceMap)
  else
    let depGraph := buildDependencyGraph graph

    match topoSortModules depGraph with
    | .cycles cyclicDeps =>
      let diags := cyclicDeps.filterMap fun cycle =>
        cycle.imports[0]?.map fun edge =>
          let msg := s!"Cyclic import detected: {cycle.modules.toList}"
          Diagnostic.error msg edge.importSpan
      pure (ProjectResult.failed packageName diags sourceMap)

    | .sorted sortedNames =>
      match ← loadDeps config.deps with
      | .error e =>
        pure (ProjectResult.failed packageName #[Diagnostic.error (toString e) Span.uninhabited] sourceMap)

      | .ok deps =>
        let (extSymbols, extInstances, extConstructors) := processExternalDependencies deps

        -- Optionally inject prelude
        let preludeSymbols := extractPreludeSymbols extSymbols
        let graph := if preludeSymbols.isEmpty then graph
                     else injectPreludeIntoGraph preludeSymbols graph

        let supply := UniqueSupply.initial packageName

        let (checkDiags, checkedModules, _) := checkModulesInOrder
          sortedNames graph extSymbols extInstances packageName supply

        let symbols := checkedModules.foldl (init := {}) fun acc m =>
          m.publicSymbols.fold (init := acc) fun env sym qt => env.insert sym qt
        let instances := checkedModules.foldl (init := {}) fun acc m =>
          mergeInstanceEnvs acc m.publicInstances
        let constructors := checkedModules.foldl (init := {}) fun acc m =>
          m.constructorMetadata.fold (init := acc) fun env n tag => env.insert n tag

        let allDiags := parseDiags ++ checkDiags

        if allDiags.hasErrors then
          pure (ProjectResult.failed packageName allDiags sourceMap)
        else
          pure (ProjectResult.succeeded packageName allDiags checkedModules symbols instances constructors sourceMap)

/-- Check a project (file or directory) -/
def checkProject
    (config : ProjectConfig)
    (loadDeps : Array (String × System.FilePath) → IO (Except CheckError (Array ExternalDependency)))
    : IO ProjectResult := do
  if ← config.input.isDir then
    checkDirectory config loadDeps
  else if config.input.extension == some "soma" then
    checkSingleFile config loadDeps
  else
    let msg := s!"Input is neither a .soma file nor a directory: {config.input}"
    let name := config.name.getD "unknown"
    pure (ProjectResult.failed name #[Diagnostic.error msg Span.uninhabited])

end Soma.Check
