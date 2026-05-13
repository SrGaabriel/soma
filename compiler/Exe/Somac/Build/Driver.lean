import Somac.Build.Pipeline
import Somac.Build.External
import Somac.Build.Package
import Soma.Project
import Soma.Project.Check
import Soma.Driver.Options
import Soma.Driver.Target
import Soma.Diagnostic

namespace Somac.Build

open Soma
open Soma.Project
open Soma.Driver
open Soma (Diagnostic Diagnostics DiagContext severity)
open Soma.Syntax (Span)
open Soma.Project.Check

/-- Result of a build operation -/
structure BuildResult where
  success : Bool
  diagnostics : Array Diagnostic
  outputPath : Option System.FilePath := none
  diagCtx : DiagContext := DiagContext.empty

namespace BuildResult

def failed (diags : Array Diagnostic)
    (diagCtx : DiagContext := DiagContext.empty)
    : BuildResult :=
  { success := false, diagnostics := diags, diagCtx }

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
    (targetSpec : TargetSpec)
    : IO (Except String Unit) := do
  let ext := outputPath.extension
  let tools := External.defaultTools
  let optLevel := opts.resolvedOptLevel
  let llvmTarget := some targetSpec.llvmTarget

  match ext with
  | some "ll" =>
    IO.FS.writeFile outputPath llvmIR
    IO.println s!"Generated LLVM IR: {outputPath}"
    pure (.ok ())

  | some "o" =>
    let llTemp := outputPath.withExtension "ll"
    IO.FS.writeFile llTemp llvmIR
    let result ← External.compileToObject tools llTemp outputPath optLevel opts.lto llvmTarget
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
      let result ← External.compileAndLink tools llTemp outputPath none optLevel false opts.sysroot opts.lto llvmTarget

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
    Render.eprintAllCtx result.diagCtx result.diagnostics

  if !result.success then
    IO.eprintln ""
    IO.eprintln (Render.summary result.diagnostics)
    pure (BuildResult.failed result.diagnostics result.diagCtx)
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

    let codegenError (e : IO.Error) : IO BuildResult := do
      let diag : Diagnostic :=
        { severity := severity .codegen
          message := e.toString
          primary := { substrate := 0
                       range := { startLine := 0, startCol := 0
                                  endLine := 0, endCol := 0 }
                       message := some e.toString
                       style := .error } }
      Render.eprintDiagCtx result.diagCtx diag
      IO.eprintln ""
      IO.eprintln (Render.summary #[diag])
      pure (BuildResult.failed #[diag] result.diagCtx)

    if opts.lib then
      try
        let compileResult ← compileLibrary
          result.packageName
          result.checkedModules
          extConstructors
          result.globals
          dependencyAlloyModules
          result.abbrevEnv
        let libPath := outputPath.withExtension "toria"
        match ← generateLibrary opts result compileResult libPath with
        | .ok () =>
          IO.println s!"Successfully built library with {result.checkedModules.size} module(s)"
          pure (BuildResult.succeeded libPath)
        | .error e =>
          IO.eprintln s!"Library packaging failed: {e}"
          pure (BuildResult.failed #[])
      catch e => codegenError e
    else
      let targetSpec ← do
        let base ← Soma.Driver.TargetSpec.resolve opts.target
        if opts.target.isNone && base.os == Soma.Driver.TargetOS.windows then
          let detected ← External.detectClangAbi External.defaultTools
          match detected with
          | .msvc => pure Soma.Driver.TargetSpec.x86_64_windows_msvc
          | _ => pure base
        else
          pure base
      let dataLayout := if targetSpec.dataLayout.isEmpty then none else some targetSpec.dataLayout
      try
        let compileResult ← compileModules
          result.packageName
          result.checkedModules
          extConstructors
          result.globals
          dependencyAlloyModules
          opts.runSomaPasses
          (some targetSpec.llvmTarget)
          targetSpec.os
          (targetSpec.pointerWidth / 8)
          dataLayout
          result.abbrevEnv
        match compileResult.llvmIR with
        | some llvmIR =>
          match ← generateOutput opts outputPath llvmIR targetSpec with
          | .ok () =>
            IO.println s!"Successfully compiled {result.checkedModules.size} module(s)"
            pure (BuildResult.succeeded outputPath)
          | .error e =>
            IO.eprintln s!"Compilation failed: {e}"
            pure (BuildResult.failed #[])
        | none =>
          IO.eprintln "Internal error: executable build produced no LLVM IR"
          pure (BuildResult.failed #[])
      catch e => codegenError e

end Somac.Build
