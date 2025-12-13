import Somac.Build.Pipeline
import Somac.Build.Compiled
import Soma.Project
import Soma.Driver.Options
import Soma.Logging
import Soma.Unique

namespace Somac.Build

open Soma
open Soma.Project
open Soma.Driver
open Soma.Logging
open Soma.Syntax (Diagnostic Diagnostics Span)
open Soma (UniqueSupply)

/-- Result of a build operation -/
structure BuildResult where
  success : Bool
  diagnostics : Array Diagnostic
  outputPath : Option System.FilePath
  compiledModules : Array CompiledModule

namespace BuildResult

def failed (diags : Array Diagnostic) : BuildResult :=
  { success := false, diagnostics := diags, outputPath := none, compiledModules := #[] }

def succeeded (path : System.FilePath) (modules : Array CompiledModule) : BuildResult :=
  { success := true, diagnostics := #[], outputPath := some path, compiledModules := modules }

end BuildResult

/-- Generate the output file path based on options -/
def generateOutputPath (opts : BuildOptions) (defaultName : String) : System.FilePath :=
  match opts.output with
  | some path => ⟨path⟩
  | none =>
    if opts.lib then
      ⟨defaultName ++ ".toria"⟩ -- Library tarball
    else
      ⟨defaultName⟩ -- Executable (no extension)

/-- Generate the final output file -/
def generateOutput (opts : BuildOptions) (outputPath : System.FilePath) (llvmIR : String) : IO Unit := do
  let ext := outputPath.extension

  match ext with
  | some "ll" =>
    IO.FS.writeFile outputPath llvmIR
    IO.println s!"Generated LLVM IR: {outputPath}"

  | some "o" =>
    let llTemp := outputPath.withExtension "ll"
    IO.FS.writeFile llTemp llvmIR
    -- TODO
    sorry
  | some "toria" =>
    -- TODO
    sorry
  | _ =>
    if opts.lib then
      -- TODO
      sorry
    else
      let llTemp := outputPath.withExtension "ll"
      IO.FS.writeFile llTemp llvmIR
      -- TODO
      sorry

/-- Build a single .soma file -/
def buildSingleFile (opts : BuildOptions) : IO BuildResult := do
  let path : System.FilePath := opts.input
  let name := opts.name.getD (path.fileStem.getD "Main")

  IO.println s!"Compiling single file: {path}"

  -- Parse the module
  match ← parseModule name path with
  | .error diags =>
    for diag in diags do
      IO.eprintln s!"  {diag.severity}: {diag.message}"
    pure (BuildResult.failed diags)

  | .ok info =>
    let graph : ModuleGraph := ({} : ModuleGraph).insert name info
    let depGraph := buildDependencyGraph graph

    -- Check for cycles
    match topoSortModules depGraph with
    | .cycles groups =>
      let msg := s!"Cyclic imports detected: {groups.map (·.toList)}"
      IO.eprintln msg
      pure (BuildResult.failed #[Diagnostic.error msg Span.uninhabited])

    | .sorted sortedNames =>
      -- Load external dependencies
      let externalDeps ← loadExternalDependencies (opts.deps.map fun (n, p) => (n, ⟨p⟩))
      match externalDeps with
      | .error e =>
        IO.eprintln s!"Failed to load dependencies: {e}"
        pure (BuildResult.failed #[Diagnostic.error (toString e) Span.uninhabited])

      | .ok deps =>
        let (extSymbols, extInstances, extConstructors) := processExternalDependencies deps

        -- Initialize UniqueSupply for this compilation unit
        let supply := UniqueSupply.initial name

        -- Compile
        let (compileDiags, compiledModules, _) := compileModulesInOrder sortedNames graph extSymbols extInstances extConstructors name supply

        if compileDiags.size > 0 then
          Error.printDiagnostics compileDiags info.sourceFile


        if Diagnostics.hasErrors compileDiags then
          IO.eprintln (Error.renderSummary compileDiags)
          pure (BuildResult.failed compileDiags)
        else
          -- Link
          let (llvmIR, _allConstructors) ← linkModules name compiledModules extConstructors

          -- Generate output
          let outputPath := generateOutputPath opts name
          generateOutput opts outputPath llvmIR

          IO.println s!"Successfully compiled: {outputPath}"
          pure (BuildResult.succeeded outputPath compiledModules)

/-- Extract prelude symbols from external dependencies -/
def extractPreludeSymbols (extSymbols : Std.HashMap String SymbolEnv) : Array String :=
  match extSymbols.get? preludeModuleName with
  | none => #[]
  | some env => env.toArray.map fun (sym, _) => sym.name

/-- Build a project directory -/
def buildDirectory (opts : BuildOptions) : IO BuildResult := do
  let rootDir : System.FilePath := opts.input
  let packageName := opts.name.getD (rootDir.fileName.getD "app")

  IO.println s!"Compiling project: {packageName} from {rootDir}"

  -- Find all modules
  let modules ← findModules packageName rootDir
  IO.println s!"Discovered {modules.size} modules"

  -- Parse all modules
  match ← parseModules modules with
  | (#[], graph) =>
    let depGraph := buildDependencyGraph graph

    -- Topological sort
    match topoSortModules depGraph with
    | .cycles groups =>
      IO.eprintln "Error: Cyclic imports detected between modules:"
      for group in groups do
        IO.eprintln s!"  {group.toList}"
      let msg := s!"Cyclic imports: {groups.map (·.toList)}"
      pure (BuildResult.failed #[Diagnostic.error msg Span.uninhabited])

    | .sorted sortedNames =>
      IO.println s!"Compilation order: {sortedNames.toList}"

      -- Load external dependencies
      let externalDeps ← loadExternalDependencies (opts.deps.map fun (n, p) => (n, ⟨p⟩))
      match externalDeps with
      | .error e =>
        IO.eprintln s!"Failed to load dependencies: {e}"
        pure (BuildResult.failed #[Diagnostic.error (toString e) Span.uninhabited])

      | .ok deps =>
        let (extSymbols, extInstances, extConstructors) := processExternalDependencies deps

        -- Optionally inject prelude
        let preludeSymbols := extractPreludeSymbols extSymbols
        let graph := if preludeSymbols.isEmpty then graph
                     else injectPreludeIntoGraph preludeSymbols graph

        -- Initialize UniqueSupply for this compilation unit
        let supply := UniqueSupply.initial packageName

        -- Compile all modules
        let (compileDiags, compiledModules, _) := compileModulesInOrder sortedNames graph extSymbols extInstances extConstructors packageName supply

        for modName in sortedNames do
          if let some info := graph.get? modName then
            let modDiags := compileDiags.filter fun _ =>
              true  -- TODO: filter by module
            if modDiags.size > 0 then
              Error.printDiagnostics modDiags info.sourceFile

        if Diagnostics.hasErrors compileDiags then
          IO.eprintln (Error.renderSummary compileDiags)
          pure (BuildResult.failed compileDiags)
        else
          -- Link
          let (llvmIR, _allConstructors) ← linkModules packageName compiledModules extConstructors

          -- Generate output
          let outputPath := generateOutputPath opts packageName
          generateOutput opts outputPath llvmIR

          IO.println s!"Successfully compiled {compiledModules.size} modules"
          IO.println s!"Output: {outputPath}"
          pure (BuildResult.succeeded outputPath compiledModules)
  | (diags, _graph) =>
    IO.eprintln "Failed to parse one or more modules:"
    for diag in diags do
      IO.eprintln s!"  {diag.severity}: {diag.message}"
    pure (BuildResult.failed diags)

/-- Main build entry point - dispatches based on input type -/
def build (opts : BuildOptions) : IO BuildResult := do
  let inputPath : System.FilePath := opts.input

  if ← inputPath.isDir then
    buildDirectory opts
  else if inputPath.extension == some "soma" then
    buildSingleFile opts
  else
    let msg := s!"Input is neither a .soma file nor a directory: {opts.input}"
    IO.eprintln msg
    pure (BuildResult.failed #[Diagnostic.error msg Span.uninhabited])

end Somac.Build
