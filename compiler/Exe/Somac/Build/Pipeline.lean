import Soma.Project.Metadata
import Soma.Project
import Soma.Project.Check
import Soma.Metal.LambdaLift
import Somac.Circuit
import Somac.Alloy
import Somac.Alloy.Merge
import Somac.Alloy.Serialize
import Somac.Llvm

namespace Somac.Build

open Soma
open Soma.Project
open Soma.Syntax
open Soma.Check

/-- Load external dependencies from metadata JSON files -/
def loadExternalDependencies (deps : Array (String × System.FilePath))
    : IO (Except CheckError (Array ExternalDependency)) :=
  if deps.isEmpty then
    pure (.ok #[])
  else
    Metadata.loadMetadataFiles deps

/-- Load Alloy IR modules from a .toria package file -/
def loadAlloyModulesFromToria (path : System.FilePath) : IO (Except String (Array (String × Alloy.Module))) := do
  let tmpDir := path.withExtension "alloy.extract.tmp"
  IO.FS.createDirAll tmpDir

  let result ← IO.Process.output {
    cmd := "tar"
    args := #["-xzf", path.toString, "-C", tmpDir.toString]
  }

  if result.exitCode != 0 then
    IO.FS.removeDirAll tmpDir |>.catchExceptions fun _ => pure ()
    return .error s!"Failed to extract tarball: {result.stderr}"

  let entries ← tmpDir.readDir
  let extractedDir := match entries.toList.head? with
    | some entry => tmpDir / entry.fileName
    | none => tmpDir

  -- Read manifest to get module names
  let manifestPath := extractedDir / "manifest.bin"
  let manifestBytes ← IO.FS.readBinFile manifestPath

  -- The manifest format is: magic (4 bytes) + serialized PackageManifest
  let manifestMagic : ByteArray := ByteArray.mk #[0x54, 0x4F, 0x52, 0x49] -- "TORI"
  if manifestBytes.size < 4 then
    IO.FS.removeDirAll tmpDir |>.catchExceptions fun _ => pure ()
    return .error "Invalid manifest: too small"

  let magic := ByteArray.mk (manifestBytes.toList.take 4).toArray
  if magic != manifestMagic then
    IO.FS.removeDirAll tmpDir |>.catchExceptions fun _ => pure ()
    return .error "Invalid manifest: bad magic bytes"

  let alloyDir := extractedDir / "alloy"
  let mut alloyModules : Array (String × Alloy.Module) := #[]

  if ← alloyDir.pathExists then
    let packageDirs ← alloyDir.readDir
    for packageEntry in packageDirs do
      let packageDir := alloyDir / packageEntry.fileName
      if ← packageDir.isDir then
        let moduleEntries ← packageDir.readDir
        for entry in moduleEntries do
          if entry.fileName.endsWith ".alloybin" then
            let modName := s!"{packageEntry.fileName}/{entry.fileName.dropRight 9}" -- "package/module"
            let binPath := packageDir / entry.fileName
            match ← Alloy.Serialize.readAlloyBin binPath with
            | .ok alloyMod => alloyModules := alloyModules.push (modName, alloyMod)
            | .error e =>
              IO.FS.removeDirAll tmpDir |>.catchExceptions fun _ => pure ()
              return .error s!"Failed to read Alloy module '{modName}': {e}"

  IO.FS.removeDirAll tmpDir |>.catchExceptions fun _ => pure ()
  pure (.ok alloyModules)

/-- Load Alloy IR from all dependency .toria files -/
def loadDependencyAlloyModules (deps : Array (String × System.FilePath))
    : IO (Except String (Array (String × Alloy.Module))) := do
  if deps.isEmpty then
    pure (.ok #[])
  else
    let mut allModules : Array (String × Alloy.Module) := #[]
    for (depName, path) in deps do
      match path.extension with
      | some "toria" =>
        match ← loadAlloyModulesFromToria path with
        | .ok modules =>
          IO.println s!"  Loaded {modules.size} Alloy module(s) from dependency '{depName}'"
          allModules := allModules ++ modules
        | .error e =>
          return .error s!"Failed to load Alloy IR from '{depName}': {e}"
      | _ => pure ()
    pure (.ok allModules)

/-- Lower a single checked module to Alloy IR -/
def lowerToAlloy (cm : CheckedModule) (globals : Soma.Dependent.Globals) : Alloy.Module :=
  -- Lambda lifting
  let liftedTypedFunctions := Soma.Metal.LambdaLift.liftAll cm.typedFunctions cm.name

  -- Lower to Circuit IR
  let graph := Circuit.Lower.lower cm.metalModule.types liftedTypedFunctions cm.usages (some globals)

  -- Lower to Alloy MIR
  Alloy.Lower.lower graph cm.name

/-- Result of compilation pipeline -/
structure CompileResult where
  /-- Generated LLVM IR -/
  llvmIR : String
  /-- All constructor metadata -/
  constructors : Std.HashMap String Nat
  /-- Pre-merge Alloy modules -/
  alloyModules : Array (String × Alloy.Module)

/-- Compile checked modules to LLVM IR -/
def compileModules
    (packageName : String)
    (modules : Array CheckedModule)
    (externalConstructors : Std.HashMap String Nat)
    (mergedGlobals : Soma.Dependent.Globals)
    (dependencyAlloyModules : Array (String × Alloy.Module) := #[])
    : IO CompileResult := do
  IO.println "\n=== Starting compilation phase ==="
  IO.println s!"  Compiling {modules.size} module(s) for package '{packageName}'"

  -- Extract all constructor metadata from modules
  let mut allConstructors : Std.HashMap String Nat := externalConstructors
  for m in modules do
    let ctors := CheckedModule.constructorMetadata m
    for (name, tag) in ctors.toArray do
      allConstructors := allConstructors.insert name tag

  IO.println s!"  Collected {allConstructors.size} constructors"

  -- Lower each module to Alloy IR
  IO.println "  Lowering to Alloy IR..."
  let localAlloyModules : Array (String × Alloy.Module) := modules.map fun cm =>
    (cm.name, lowerToAlloy cm mergedGlobals)

  IO.println s!"  Generated {localAlloyModules.size} local Alloy module(s)"

  -- Combine local modules with dependency modules for merging
  let allAlloyModules := dependencyAlloyModules ++ localAlloyModules

  if dependencyAlloyModules.size > 0 then
    IO.println s!"  Including {dependencyAlloyModules.size} dependency Alloy module(s)"

  -- Merge all Alloy modules into one
  IO.println "  Merging modules..."
  let merged := Alloy.Merge.merge allAlloyModules packageName

  IO.println s!"  Merged module has {merged.funcs.size} function(s)"

  -- Monomorphize
  IO.println "  Monomorphizing..."
  let mono := Alloy.Monomorphize.monomorphize merged

  IO.println s!"  Monomorphized module has {mono.funcs.size} function(s)"

  -- Generate LLVM IR
  IO.println "  Generating LLVM IR..."
  let llvmIR := Llvm.codegenToString mono

  IO.println "Compilation phase complete"

  -- Return only local modules for library packaging (not dependencies)
  pure { llvmIR, constructors := allConstructors, alloyModules := localAlloyModules }

/-- Build ProjectMetadata from a ProjectResult for library packaging -/
def buildProjectMetadata (result : ProjectResult) : Metadata.ProjectMetadata :=
  { module := result.packageName
  , symbols := Metadata.symbolEnvToSerializable result.symbols
  , instances := Metadata.instanceMetadataToSerializable result.instances
  , constructors := Metadata.constructorsToSerializable result.constructors
  , globals := Metadata.globalsToSerializable result.globals
  , instanceEnv := Metadata.instanceEnvToSerializable result.instanceEnv
  , abbrevEnv := Metadata.abbrevEnvToSerializable result.abbrevEnv
  }

end Somac.Build
