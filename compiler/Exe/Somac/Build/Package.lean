import Somac.Alloy.Serialize
import Somac.Build.External
import Soma.Project.Metadata
import Kenosis

namespace Somac.Build.Package

open Kenosis

/-- Package manifest stored in .toria files -/
structure PackageManifest where
  /-- Package name -/
  name : String
  /-- Package version -/
  version : String := "1.0.0"
  /-- List of module names in the package -/
  modules : Array String
  /-- Exported symbols (public API) -/
  exports : Array String := #[]
  /-- Format version for compatibility checking -/
  formatVersion : Nat := 1
  deriving Serialize, Deserialize, Inhabited

/-- Magic bytes for manifest files -/
def manifestMagic : ByteArray := ByteArray.mk #[0x54, 0x4F, 0x52, 0x49] -- "TORI"

/-- Serialize a manifest to binary -/
def serializeManifest (m : PackageManifest) : ByteArray :=
  manifestMagic ++ Binary.encode m

/-- Create a .toria library package -/
def createPackage
    (name : String)
    (modules : Array (String × Alloy.Module))
    (metadata : Soma.Project.Metadata.ProjectMetadata)
    (exports : Array String)
    (outputPath : System.FilePath)
    : IO (Except String Unit) := do
  let tools := External.defaultTools

  -- Create temp directory
  let tmpDir := outputPath.withExtension "toria.tmp"
  IO.FS.createDirAll tmpDir

  -- Write manifest
  let manifest : PackageManifest := {
    name := name
    modules := modules.map (·.1)
    exports := exports
  }
  IO.FS.writeBinFile (tmpDir / "manifest.bin") (serializeManifest manifest)

  -- Write metadata (for type checking by dependent packages)
  IO.FS.writeBinFile (tmpDir / "metadata.bin") (Binary.encode metadata)

  -- Write Alloy modules
  let alloyDir := tmpDir / "alloy"
  IO.FS.createDirAll alloyDir
  for (modName, alloyMod) in modules do
    let relPath := modName.replace "::" "/"
    let binPath := alloyDir / (relPath ++ ".alloybin")
    if let some parent := binPath.parent then
      IO.FS.createDirAll parent
    Alloy.Serialize.writeAlloyBin binPath alloyMod

  -- Create tarball
  let result ← External.createTarball tools tmpDir outputPath

  -- Cleanup temp directory
  IO.FS.removeDirAll tmpDir |>.catchExceptions fun _ => pure ()

  pure result

/-- Contents of a loaded .toria package -/
structure LoadedPackage where
  manifest : PackageManifest
  metadata : Soma.Project.Metadata.ProjectMetadata
  alloyModules : Array (String × Alloy.Module)

end Somac.Build.Package
