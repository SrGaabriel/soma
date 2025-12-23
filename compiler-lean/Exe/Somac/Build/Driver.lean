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
    for diag in result.diagnostics do
      IO.eprintln s!"  {diag.severity}: {diag.message}"

  if !result.success then
    IO.eprintln (Error.renderSummary result.diagnostics)
    pure (BuildResult.failed result.diagnostics)
  else
    -- Link
    let extConstructors : Std.HashMap String Nat := {}  -- TODO: get from deps
    let (llvmIR, _allConstructors) ← linkModules result.packageName result.checkedModules extConstructors

    -- Generate output
    let outputPath := generateOutputPath opts result.packageName
    generateOutput opts outputPath llvmIR

    IO.println s!"Successfully compiled {result.checkedModules.size} modules"
    IO.println s!"Output: {outputPath}"
    pure BuildResult.succeeded

end Somac.Build
