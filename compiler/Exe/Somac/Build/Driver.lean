import Somac.Build.Pipeline
import Somac.Build.External
import Somac.Build.Package
import Soma.Project
import Soma.Project.Check
import Soma.Driver.Options
import Soma.Logging

namespace Somac.Build

open Soma
open Soma.Project
open Soma.Driver
open Soma.Logging
open Soma.Syntax (Diagnostic Diagnostics Span)
open Soma.Project.Check

/-- Result of a build operation -/
structure BuildResult where
  success : Bool
  diagnostics : Array Diagnostic
  outputPath : Option System.FilePath := none

namespace BuildResult

def failed (diags : Array Diagnostic) : BuildResult :=
  { success := false, diagnostics := diags }

def succeeded (output : System.FilePath) : BuildResult :=
  { success := true, diagnostics := #[], outputPath := some output }

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
def generateOutput
    (opts : BuildOptions)
    (outputPath : System.FilePath)
    (llvmIR : String)
    : IO (Except String Unit) := do
  let ext := outputPath.extension
  let tools := External.defaultTools
  let optLevel := opts.resolvedOptLevel

  match ext with
  | some "ll" =>
    IO.FS.writeFile outputPath llvmIR
    IO.println s!"Generated LLVM IR: {outputPath}"
    pure (.ok ())

  | some "o" =>
    let llTemp := outputPath.withExtension "ll"
    IO.FS.writeFile llTemp llvmIR
    let result ← External.compileToObject tools llTemp outputPath optLevel opts.lto
    if !opts.emitLlvm then
      IO.FS.removeFile llTemp |>.catchExceptions fun _ => pure ()
    else
      IO.println s!"LLVM IR saved to: {llTemp}"
    match result with
    | .ok () =>
      IO.println s!"Generated object file: {outputPath}"
      pure (.ok ())
    | .error e =>
      pure (.error e)

  | _ =>
      let llTemp := outputPath.withExtension "ll"
      IO.FS.writeFile llTemp llvmIR

      IO.println s!"Compiling to executable..."
      let result ← External.compileAndLink tools llTemp outputPath none optLevel false opts.sysroot opts.lto

      match result with
      | .ok () =>
        if !opts.emitLlvm then
          IO.FS.removeFile llTemp |>.catchExceptions fun _ => pure ()
        else
          IO.println s!"LLVM IR saved to: {llTemp}"
        IO.println s!"Generated executable: {outputPath}"
        pure (.ok ())
      | .error e =>
        IO.println s!"LLVM IR saved to: {llTemp}"
        pure (.error e)

/-- Generate a .toria library package -/
def generateLibrary
    (opts : BuildOptions)
    (result : ProjectResult)
    (compileResult : CompileResult)
    (outputPath : System.FilePath)
    : IO (Except String Unit) := do
  IO.println "  Creating library package..."

  -- Build metadata for dependent packages
  let metadata := buildProjectMetadata result

  -- Collect exported symbols (all public symbols)
  let exports := result.symbols.fold (init := #[]) fun acc sym _ =>
    acc.push sym.name

  -- Optionally emit LLVM IR
  if opts.emitLlvm then
    if let some llvmIR := compileResult.llvmIR then
      let llPath := outputPath.withExtension "ll"
      IO.FS.writeFile llPath llvmIR
      IO.println s!"LLVM IR saved to: {llPath}"

  -- Create .toria package
  Package.createPackage
    result.packageName
    compileResult.alloyModules
    metadata
    exports
    outputPath

/-- Main build entry point -/
def build (opts : BuildOptions) : IO BuildResult := do
  let inputPath : System.FilePath := opts.input

  IO.println s!"Building: {inputPath}"

  let config : ProjectConfig := {
    input := inputPath
    name := opts.name
    deps := opts.deps.map fun (n, p) => (n, ⟨p⟩)
  }

  let result ← checkProject config loadExternalDependencies

  -- Print diagnostics
  if result.diagnostics.size > 0 then
    for (_, sourceFile) in result.sourceFiles.files do
      Error.printDiagnostics result.diagnostics sourceFile

  if !result.success then
    IO.eprintln ""
    IO.eprintln (Error.renderSummary result.diagnostics)
    pure (BuildResult.failed result.diagnostics)
  else
    let dependencyAlloyModules ← if opts.deps.isEmpty then
      pure #[]
    else do
      IO.println "  Loading dependency Alloy IR..."
      let depsWithPaths := opts.deps.map fun (n, p) => (n, (⟨p⟩ : System.FilePath))
      match ← loadDependencyAlloyModules depsWithPaths with
      | .ok modules => pure modules
      | .error e =>
        IO.eprintln s!"Failed to load dependency Alloy IR: {e}"
        pure #[]

    -- Generate output
    let outputPath := generateOutputPath opts result.packageName
    let extConstructors : Std.HashMap String Nat := result.constructors

    if opts.lib then
      let compileResult ← compileLibrary
        result.packageName
        result.checkedModules
        extConstructors
        result.globals
        dependencyAlloyModules
      let libPath := outputPath.withExtension "toria"
      match ← generateLibrary opts result compileResult libPath with
      | .ok () =>
        IO.println s!"Successfully built library with {result.checkedModules.size} module(s)"
        pure (BuildResult.succeeded libPath)
      | .error e =>
        IO.eprintln s!"Library packaging failed: {e}"
        pure (BuildResult.failed #[])
    else
      let compileResult ← compileModules
        result.packageName
        result.checkedModules
        extConstructors
        result.globals
        dependencyAlloyModules
        opts.runSomaPasses
      match compileResult.llvmIR with
      | some llvmIR =>
        match ← generateOutput opts outputPath llvmIR with
        | .ok () =>
          IO.println s!"Successfully compiled {result.checkedModules.size} module(s)"
          pure (BuildResult.succeeded outputPath)
        | .error e =>
          IO.eprintln s!"Compilation failed: {e}"
          pure (BuildResult.failed #[])
      | none =>
        IO.eprintln "Internal error: executable build produced no LLVM IR"
        pure (BuildResult.failed #[])

end Somac.Build
