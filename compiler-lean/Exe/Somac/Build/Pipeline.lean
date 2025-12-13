import Somac.Build.Compiled
import Soma.Project
import Soma.Syntax
import Soma.Metal
import Soma.Logging

namespace Somac.Build

open Soma
open Soma.Project
open Soma.Syntax
open Soma.Metal
open Soma.Logging

/-- Result of parsing a single module -/
abbrev ParseResult := Except (Array Diagnostic) ModuleInfo

/-- Parse a single source file into a ModuleInfo -/
def parseModule (moduleName : String) (path : System.FilePath) : IO ParseResult := do
  let content ← IO.FS.readFile path
  let sourceFile := SourceFile.create ⟨0⟩ path.toString content

  -- Lex
  let (tokens, lexDiags) := lexCode sourceFile

  -- Parse
  let (cst, parseDiags) := Parse.parseSourceFile.run' tokens sourceFile

  -- Lower to AST
  let baseName := moduleName.splitOn "/" |>.getLast!
  let (astOpt, lowerDiags) := lower cst baseName

  let allDiags := lexDiags ++ parseDiags ++ lowerDiags

  match astOpt with
  | none => pure (.error allDiags)
  | some ast =>
    if allDiags.hasErrors then
      pure (.error allDiags)
    else
      let modName := ModuleName.fromString moduleName
      pure (.ok {
        name := modName
        path := path
        content := content
        sourceFile := sourceFile
        ast := ast
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

/-- Compile a single module with access to already-compiled dependencies -/
def compileModule
    (_packageName : String)
    (info : ModuleInfo)
    (compiledDeps : Std.HashMap String CompiledModule)
    (externalDeps : Std.HashMap String SymbolEnv)
    (externalInstances : Std.HashMap String InstanceEnv)
    (_externalConstructors : Std.HashMap String Nat)
    : IO (Except CompileError CompiledModule) := do
  let modName := info.name.toString

  IO.println s!"Compiling module: {modName}"

  -- Collect seed environment from dependencies
  let seedEnv : SymbolEnv := compiledDeps.fold (init := {}) fun acc _ dep =>
    acc.fold (init := dep.publicSymbols) fun env sym ty => env.insert sym ty

  let seedEnv := externalDeps.fold (init := seedEnv) fun acc _ env =>
    acc.fold (init := env) fun e sym ty => e.insert sym ty

  let seedInstances : InstanceEnv := compiledDeps.fold (init := {}) fun acc _ dep =>
    mergeInstanceEnvs acc dep.publicInstances

  let seedInstances := externalInstances.fold (init := seedInstances) fun acc _ env =>
    mergeInstanceEnvs acc env

  -- TODO

  let placeholderModule : CompiledModule := {
    name := modName
    metalNormalized := Metal.Module.empty modName
    publicSymbols := seedEnv  -- TODO: Should be newly defined symbols
    publicInstances := seedInstances  -- TODO: Should be newly defined instances
    resolvedAst := info.ast
  }

  pure (.ok placeholderModule)
where
  mergeInstanceEnvs (e1 e2 : InstanceEnv) : InstanceEnv :=
    e2.fold (init := e1) fun acc className instances =>
      match acc.get? className with
      | none => acc.insert className instances
      | some existing => acc.insert className (existing ++ instances)

/-- Compile all modules in topological order -/
def compileModulesInOrder
    (sortedNames : Array String)
    (graph : ModuleGraph)
    (externalDeps : Std.HashMap String SymbolEnv)
    (externalInstances : Std.HashMap String InstanceEnv)
    (externalConstructors : Std.HashMap String Nat)
    (packageName : String)
    : IO (Except CompileError (Array CompiledModule)) := do
  let mut compiled : Std.HashMap String CompiledModule := {}
  let mut results : Array CompiledModule := #[]

  for modName in sortedNames do
    match graph.get? modName with
    | none => pure () -- Skip missing modules (shouldn't happen)
    | some info =>
      match ← compileModule packageName info compiled externalDeps externalInstances externalConstructors with
      | .error e => return .error e
      | .ok cm =>
        compiled := compiled.insert modName cm
        results := results.push cm

  pure (.ok results)

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

/-- Load external dependencies from tarball files -/
def loadExternalDependencies (deps : Array (String × System.FilePath))
    : IO (Except CompileError (Array ExternalDependency)) := do
  let mut results : Array ExternalDependency := #[]

  for (name, path) in deps do
    -- Check if path exists
    if !(← path.pathExists) then
      return .error (.dependencyNotFound name path.toString)

    IO.println s!"Loading external dependency: {name} from {path}"

    -- TODO

    results := results.push {
      name := name
      version := none
      symbols := {}
      instances := {}
      constructors := {}
    }

  pure (.ok results)

/-- Process external dependencies into lookup tables -/
def processExternalDependencies (deps : Array ExternalDependency)
    : (Std.HashMap String SymbolEnv × Std.HashMap String InstanceEnv × Std.HashMap String Nat) :=
  deps.foldl (init := ({}, {}, {})) fun (symbols, instances, constructors) dep =>
    let symbols' := dep.symbols.fold (init := symbols) fun acc modName env =>
      acc.insert modName env
    let instances' := dep.instances.fold (init := instances) fun acc modName env =>
      acc.insert modName env
    let constructors' := dep.constructors.fold (init := constructors) fun acc ctorName tag =>
      acc.insert ctorName tag
    (symbols', instances', constructors')

end Somac.Build
