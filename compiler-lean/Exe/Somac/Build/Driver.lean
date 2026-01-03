import Somac.Build.Pipeline
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
open Soma.Check

/-- Result of a build operation -/
structure BuildResult where
  success : Bool
  diagnostics : Array Diagnostic

namespace BuildResult

def failed (diags : Array Diagnostic) : BuildResult :=
  { success := false, diagnostics := diags }

def succeeded : BuildResult :=
  { success := true, diagnostics := #[] }

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
    IO.println s!"Generated LLVM IR: {llTemp}"
    IO.println s!"Note: Object file generation not yet implemented"

  | some "toria" =>
    -- For now, just write the LLVM IR as the library content
    IO.FS.writeFile outputPath llvmIR
    IO.println s!"Generated library archive: {outputPath}"

  | _ =>
    if opts.lib then
      let libPath := outputPath.withExtension "toria"
      IO.FS.writeFile libPath llvmIR
      IO.println s!"Generated library archive: {libPath}"
    else
      let llTemp := outputPath.withExtension "ll"
      IO.FS.writeFile llTemp llvmIR
      IO.println s!"Generated LLVM IR: {llTemp}"
      IO.println s!"Note: Executable generation not yet implemented"

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
    -- Link modules
    let extConstructors : Std.HashMap String Nat := result.constructors
    let (llvmIR, _allConstructors) ← linkModules result.packageName result.checkedModules extConstructors

    -- Generate output
    let outputPath := generateOutputPath opts result.packageName
    generateOutput opts outputPath llvmIR

    IO.println s!"Successfully compiled {result.checkedModules.size} module(s)"
    IO.println s!"Output: {outputPath}"
    pure BuildResult.succeeded

end Somac.Build
