import Somac.Build.Pipeline
import Soma.Project
import Soma.Project.Check
import Soma.Project.Metadata
import Soma.Driver.Options
import Kenosis

namespace Somac.Build.Metadata

open Soma
open Soma.Project
open Soma.Project.Metadata
open Soma.Driver
open Soma.Syntax (Diagnostic)
open Soma.Project.Check
open Kenosis

/-- Result of metadata generation -/
structure MetadataResult where
  success : Bool
  diagnostics : Array Diagnostic
  metadata : Option ProjectMetadata
  sourceFiles : Soma.Syntax.SourceFileMap := Soma.Syntax.SourceFileMap.empty

namespace MetadataResult

def failed (diags : Array Diagnostic)
    (sourceFiles : Soma.Syntax.SourceFileMap := Soma.Syntax.SourceFileMap.empty)
    : MetadataResult :=
  { success := false, diagnostics := diags, metadata := none, sourceFiles }

def succeeded (pm : ProjectMetadata) : MetadataResult :=
  { success := true, diagnostics := #[], metadata := some pm }

end MetadataResult

/-! ## Main Entry Point -/

/-- Generate metadata for a project (file or directory) -/
def metadata (opts : MetadataOptions) (loadDeps : Array (String × System.FilePath) → IO (Except CheckError (Array ExternalDependency))) : IO MetadataResult := do
  let config : ProjectConfig := {
    input := opts.input
    name := opts.name
    deps := opts.deps.map fun (n, p) => (n, ⟨p⟩)
  }

  let result ← checkProject config loadDeps

  if result.success then
    let pm : ProjectMetadata := {
      module := result.packageName
      symbols := symbolEnvToSerializable result.symbols
      instances := instanceMetadataToSerializable result.instances
      constructors := constructorsToSerializable result.constructors
      globals := globalsToSerializable result.globals
      instanceEnv := instanceEnvToSerializable result.instanceEnv
      abbrevEnv := abbrevEnvToSerializable result.abbrevEnv
    }
    pure (MetadataResult.succeeded pm)
  else
    pure (MetadataResult.failed result.diagnostics result.sourceFiles)

end Somac.Build.Metadata
