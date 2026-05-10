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

/-- Deserialize a manifest from binary -/
def deserializeManifest (bytes : ByteArray) : Except String PackageManifest := do
  if bytes.size < 4 then
    throw "Invalid manifest: too small"
  let magic := ByteArray.mk (bytes.toList.take 4).toArray
  if magic != manifestMagic then
    throw "Invalid manifest: bad magic bytes"
  let payload := ByteArray.mk (bytes.toList.drop 4).toArray
  match Binary.decode payload with
  | .ok m => .ok m
  | .error e => throw s!"Manifest deserialization error: {e}"

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

/-- Load a .toria library package -/
def loadPackage (path : System.FilePath) : IO (Except String LoadedPackage) := do
  let tools := External.defaultTools

  -- Create temp directory for extraction
  let tmpDir := path.withExtension "extract.tmp"
  IO.FS.createDirAll tmpDir

  -- Extract tarball
  match ← External.extractTarball tools path tmpDir with
  | .error e =>
    IO.FS.removeDirAll tmpDir |>.catchExceptions fun _ => pure ()
    pure (.error s!"Failed to extract package: {e}")
  | .ok () =>
    -- Find the extracted directory (tar creates a subdirectory)
    let entries ← tmpDir.readDir
    let extractedDir := match entries.toList.head? with
      | some entry => tmpDir / entry.fileName
      | none => tmpDir

    -- Read manifest
    let manifestBytes ← IO.FS.readBinFile (extractedDir / "manifest.bin")
    let manifest ← match deserializeManifest manifestBytes with
      | .ok m => pure m
      | .error e =>
        IO.FS.removeDirAll tmpDir |>.catchExceptions fun _ => pure ()
        return .error s!"Failed to read manifest: {e}"

    -- Read metadata
    let metadataBytes ← IO.FS.readBinFile (extractedDir / "metadata.bin")
    let metadata ← match Binary.decode metadataBytes with
      | .ok (m : Soma.Project.Metadata.ProjectMetadata) => pure m
      | .error e =>
        IO.FS.removeDirAll tmpDir |>.catchExceptions fun _ => pure ()
        return .error s!"Failed to read metadata: {e}"

    -- Read Alloy modules
    let alloyDir := extractedDir / "alloy"
    let mut alloyModules : Array (String × Alloy.Module) := #[]

    for modName in manifest.modules do
      let relPath := modName.replace "::" "/"
      let binPath := alloyDir / (relPath ++ ".alloybin")
      match ← Alloy.Serialize.readAlloyBin binPath with
      | .ok alloyMod => alloyModules := alloyModules.push (modName, alloyMod)
      | .error e =>
        IO.FS.removeDirAll tmpDir |>.catchExceptions fun _ => pure ()
        return .error s!"Failed to read Alloy module '{modName}': {e}"

    IO.FS.removeDirAll tmpDir |>.catchExceptions fun _ => pure ()

    pure (.ok { manifest, metadata, alloyModules })

end Somac.Build.Package
