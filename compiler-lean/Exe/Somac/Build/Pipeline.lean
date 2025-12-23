import Somac.Build.Compiled
import Somac.Build.MetadataLoad
import Soma.Project
import Soma.Syntax
import Soma.Metal
import Soma.Infer
import Soma.Logging
import Soma.Unique
import Soma.Project.Check

namespace Somac.Build

open Soma
open Soma.Project
open Soma.Syntax
open Soma.Metal
open Soma.Typing
open Soma.Logging
open Soma (UniqueSupply)
open Soma.Check (toAst metal metalWithExternals infer buildTypeEnv buildInstanceEnv)

/-- Result of parsing a single module -/
abbrev ParseResult := Except (Array Diagnostic) ModuleInfo

/-- Parse a single source file into a ModuleInfo -/
def parseModule (moduleName : String) (path : System.FilePath) : IO ParseResult := do
  let content ← IO.FS.readFile path
  let (parseRes, lowerRes) := toAst path.toString content
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
def parseModules (modules : Array (String × System.FilePath)) : IO ((Array Diagnostic) × ModuleGraph) := do
  let mut graph : ModuleGraph := {}
  let mut allDiags : Array Diagnostic := #[]

  for (name, path) in modules do
    match ← parseModule name path with
    | .ok info => graph := graph.insert name info
    | .error diags => allDiags := allDiags ++ diags

  pure (allDiags, graph)

/-- Merge two instance environments -/
def mergeInstanceEnvs (e1 e2 : Project.InstanceEnv) : Project.InstanceEnv :=
  e2.fold (init := e1) fun acc className instances =>
    match acc.get? className with
    | none => acc.insert className instances
    | some existing => acc.insert className (existing ++ instances)

/-- Convert Project.InstanceEnv to Infer.InstanceEnv -/
def projectToInferInstanceEnv (projEnv : Project.InstanceEnv) : Infer.InstanceEnv :=
  projEnv.fold (init := Infer.InstanceEnv.empty) fun acc className instances =>
    instances.foldl (fun env (typeArgs, sym) =>
      -- Create a TyCon for the class from the symbol's unique
      let classTyCon := TyCon.mkUser sym.module className sym.unique.id
      let instDecl : Infer.InstanceDecl := {
        className := classTyCon
        args := typeArgs
        typeVars := #[] -- extracted during inference
        constraints := #[]  -- resolved during inference
        id := env.nextId
        span := sym.span
      }
      env.addInstance instDecl
    ) acc

/-- Convert SymbolEnv to array of function info for Infer.buildTypeEnvFromModule -/
def symbolEnvToFunctionInfos (seed : SymbolEnv) : Array (String × Infer.FunctionInfo) :=
  seed.fold (init := #[]) fun acc sym qt =>
    let metalName : Metal.Name := .user { id := sym.unique.id, module := sym.unique.module, original := sym.name }
    acc.push (sym.name, { qualType := qt, metalName := metalName })

/-- Convert SymbolEnv to Metal.Lower.GlobalEnv for pre-populating external symbols.
    This allows Metal lowering to resolve references to external symbols. -/
def symbolEnvToGlobalEnv (moduleName : String) (seed : SymbolEnv) : Metal.Lower.GlobalEnv :=
  seed.fold (init := Metal.Lower.GlobalEnv.empty moduleName) fun acc sym _qt =>
    let metalName : Metal.Name := .user { id := sym.unique.id, module := sym.unique.module, original := sym.name }
    let globalInfo : Metal.Lower.GlobalInfo := {
      name := metalName
      typeSyntax := none  -- Type will be resolved during inference
      definedAt := sym.span
    }
    acc.addGlobal sym.name globalInfo

/-- Extract public symbols from a typed module -/
def extractPublicSymbols (m : Metal.Module) (seed : SymbolEnv) : SymbolEnv :=
  m.functions.foldl (init := seed) fun acc fn =>
    -- Extract the unique from the function's Metal.Name
    let unique := fn.name.baseUnique?.getD { id := 0, module := m.name, original := fn.name.display }
    let sym : Symbol := {
      unique := unique
      name := fn.name.display
      kind := .binding
      module := m.name
      package := "" -- todo
      span := Span.uninhabited
    }
    acc.insert sym fn.qualifiedType

/-- Extract public instances from a typed module -/
def extractPublicInstances (m : Metal.Module) (seed : Project.InstanceEnv) (supply : UniqueSupply)
    : Project.InstanceEnv × UniqueSupply := Id.run do
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
      package := "" -- todo
      span := Span.uninhabited
    }
    match acc.get? inst.className with
    | none => acc := acc.insert inst.className #[(#[inst.instanceType], sym)]
    | some existing => acc := acc.insert inst.className (existing.push (#[inst.instanceType], sym))
  return (acc, sup)

/-- Compile a single module with access to already-compiled dependencies -/
def compileModule
    (_packageName : String)
    (info : ModuleInfo)
    (compiledDeps : Std.HashMap String CompiledModule)
    (externalDeps : Std.HashMap String SymbolEnv)
    (externalInstances : Std.HashMap String Project.InstanceEnv)
    (_externalConstructors : Std.HashMap String Nat)
    (supply : UniqueSupply)
    : (Array Diagnostic) × CompiledModule × UniqueSupply :=
  let modName := info.name.toString

  -- Collect seed environment from dependencies
  let seedEnv : SymbolEnv := compiledDeps.fold (init := {}) fun acc _ dep =>
    dep.publicSymbols.fold (init := acc) fun env sym ty => env.insert sym ty

  let seedEnv := externalDeps.fold (init := seedEnv) fun acc _ env =>
    env.fold (init := acc) fun e sym ty => e.insert sym ty

  let seedInstances : Project.InstanceEnv := compiledDeps.fold (init := {}) fun acc _ dep =>
    mergeInstanceEnvs acc dep.publicInstances

  let seedInstances := externalInstances.fold (init := seedInstances) fun acc _ env =>
    mergeInstanceEnvs acc env

  -- Convert seed symbols to GlobalEnv for Metal lowering
  let initialGlobalEnv := symbolEnvToGlobalEnv modName seedEnv

  -- Metal lowering with external symbols pre-populated
  let metalRes := metalWithExternals info.ast initialGlobalEnv

  -- Build environments with external dependencies
  let externalFunctions := symbolEnvToFunctionInfos seedEnv
  let (typeEnv, supply) := buildTypeEnv metalRes.module externalFunctions supply
  let inferInstanceEnv := buildInstanceEnv metalRes.module (projectToInferInstanceEnv seedInstances) typeEnv

  -- Type inference
  let inferRes := infer metalRes.module typeEnv inferInstanceEnv

  let allDiags := metalRes.diagnostics ++ inferRes.diagnostics

  let publicSymbols := extractPublicSymbols inferRes.module seedEnv
  let (publicInstances, supply) := extractPublicInstances inferRes.module seedInstances supply

  let compiledModule : CompiledModule := {
    name := modName
    metalNormalized := inferRes.module
    publicSymbols := publicSymbols
    publicInstances := publicInstances
    resolvedAst := info.ast
  }

  (allDiags, compiledModule, supply)

/-- Compile all modules in topological order.
    Returns accumulated diagnostics and compiled modules.

    Takes and returns UniqueSupply to ensure globally unique IDs across all modules. -/
def compileModulesInOrder
    (sortedNames : Array String)
    (graph : ModuleGraph)
    (externalDeps : Std.HashMap String SymbolEnv)
    (externalInstances : Std.HashMap String Project.InstanceEnv)
    (externalConstructors : Std.HashMap String Nat)
    (packageName : String)
    (supply : UniqueSupply)
    : (Array Diagnostic) × (Array CompiledModule) × UniqueSupply :=
  let (allDiags, _, results, finalSupply) := sortedNames.foldl
    (init := (#[], ({} : Std.HashMap String CompiledModule), #[], supply))
    fun (diags, compiled, results, sup) modName =>
      match graph.get? modName with
      | none => (diags, compiled, results, sup) -- Skip missing modules
      | some info =>
        let (moduleDiags, cm, sup') := compileModule packageName info compiled externalDeps externalInstances externalConstructors sup
        (diags ++ moduleDiags, compiled.insert modName cm, results.push cm, sup')
  (allDiags, results, finalSupply)

/-- Link compiled modules into a single optimized unit -/
def linkModules
    (packageName : String)
    (modules : Array CompiledModule)
    (_externalConstructors : Std.HashMap String Nat)
    -- TODO: Add external Alloy modules parameter
    : IO (String × Std.HashMap String Nat) := do
  IO.println "\n=== Starting link-time optimization phase ==="

  -- Fuse all Metal modules
  -- TODO: Implement actual module fusion
  IO.println s!"  Linking {modules.size} modules into package '{packageName}'"

  -- Extract all constructor metadata
  let mut allConstructors : Std.HashMap String Nat := {}
  for m in modules do
    let ctors := m.constructorMetadata
    for (name, tag) in ctors.toArray do
      allConstructors := allConstructors.insert name.display tag

  -- TODO: Return actual Alloy module
  let placeholderLLVM := s!"; Placeholder LLVM IR for {packageName}\n"

  IO.println "Link-time optimization complete (placeholder)"

  pure (placeholderLLVM, allConstructors)

/-- Load external dependencies from metadata JSON files -/
def loadExternalDependencies (deps : Array (String × System.FilePath))
    : IO (Except CompileError (Array ExternalDependency)) := do
  if deps.isEmpty then
    pure (.ok #[])
  else
    MetadataLoad.loadMetadataFiles deps

/-- Process external dependencies into lookup tables -/
def processExternalDependencies (deps : Array ExternalDependency)
    : (Std.HashMap String SymbolEnv × Std.HashMap String Project.InstanceEnv × Std.HashMap String Nat) :=
  deps.foldl (init := ({}, {}, {})) fun (symbols, instances, constructors) dep =>
    let symbols' := dep.symbols.fold (init := symbols) fun acc modName env =>
      acc.insert modName env
    let instances' := dep.instances.fold (init := instances) fun acc modName env =>
      acc.insert modName env
    let constructors' := dep.constructors.fold (init := constructors) fun acc ctorName tag =>
      acc.insert ctorName tag
    (symbols', instances', constructors')

end Somac.Build
