import Soma.Project
import Soma.Project.Check
import Soma.Core.Value
import Soma.Core.Level
import Soma.Core.Quantity
import Soma.Core.Primitive
import Soma.Dependent.Monad
import Kenosis

namespace Soma.Project.Metadata

open Soma
open Soma.Project
open Soma.Syntax (Span)
open Soma.Core
open Soma.Project.Check (ExternalDependency CheckError)
open Soma.Dependent (Globals GlobalInfo InstanceEnv InstanceInfo ClassInfo AbbrevEnv AbbrevInfo)
open Kenosis

/-- Serializable symbol entry -/
structure SymbolEntry where
  symbol : Symbol
  type : Value
  deriving Serialize, Deserialize

/-- Serializable instance entry -/
structure InstanceEntry where
  typeArgs : Array Value
  symbol : Symbol
  deriving Serialize, Deserialize

/-- Serializable instance metadata entry (class -> instances) -/
structure InstanceMetadataEntry where
  className : String
  instances : Array InstanceEntry
  deriving Serialize, Deserialize

/-- Serializable constructor entry -/
structure ConstructorEntry where
  name : String
  tag : Nat
  deriving Serialize, Deserialize

/-- Serializable global definition entry -/
structure GlobalDefEntry where
  namespacePath : Array String
  displayName : String
  info : GlobalInfo
  deriving Serialize, Deserialize

/-- Serializable inductive metadata entry -/
structure InductiveEntry where
  typeQN : Soma.Core.QualifiedName
  info : Soma.Dependent.InductiveMeta
  deriving Serialize, Deserialize

/-- Serializable constructor-to-inductive reverse index entry -/
structure CtorOwnerEntry where
  ctorName : Soma.Core.QualifiedName
  inductiveQN : Soma.Core.QualifiedName
  deriving Serialize, Deserialize

/-- Serializable wired-in entry: maps a role to its registered declarations -/
structure WiredInEntry where
  role : Soma.Dependent.WiredRole
  infos : Array GlobalInfo
  deriving Serialize, Deserialize

/-- Serializable globals -/
structure SerializableGlobals where
  defs : Array GlobalDefEntry := #[]
  anonymousDefs : Array GlobalInfo := #[]
  inductives : Array InductiveEntry := #[]
  ctorOwners : Array CtorOwnerEntry := #[]
  wiredIns : Array WiredInEntry := #[]
  deriving Serialize, Deserialize

/-- Serializable class entry -/
structure ClassEntry where
  classId : Unique
  info : ClassInfo
  deriving Serialize, Deserialize

/-- Serializable instance array entry -/
structure InstanceArrayEntry where
  classId : Unique
  instances : Array InstanceInfo
  deriving Serialize, Deserialize

/-- Serializable instance environment -/
structure SerializableInstanceEnv where
  classes : Array ClassEntry
  instances : Array InstanceArrayEntry
  nextInstanceId : Nat
  moduleName : String
  deriving Serialize, Deserialize

/-- Serializable abbreviation environment -/
structure SerializableAbbrevEnv where
  abbrevs : Array AbbrevInfo
  deriving Serialize, Deserialize

/-- Project metadata structure for JSON serialization -/
structure ProjectMetadata where
  version : String := "4" -- Version 4 uses Kenosis serialization
  module : String
  symbols : Array SymbolEntry
  instances : Array InstanceMetadataEntry
  constructors : Array ConstructorEntry
  globals : SerializableGlobals
  instanceEnv : SerializableInstanceEnv
  abbrevEnv : SerializableAbbrevEnv
  deriving Serialize, Deserialize

/-- Convert SymbolEnv to serializable form -/
def symbolEnvToSerializable (env : SymbolEnv) : Array SymbolEntry :=
  env.fold (init := #[]) fun acc sym val =>
    acc.push { symbol := sym, type := val }

/-- Convert InstanceMetadata to serializable form -/
def instanceMetadataToSerializable (env : InstanceMetadata) : Array InstanceMetadataEntry :=
  env.fold (init := #[]) fun acc className instances =>
    let entries := instances.map fun (typeArgs, sym) => { typeArgs, symbol := sym }
    acc.push { className, instances := entries }

/-- Convert constructor HashMap to serializable form -/
def constructorsToSerializable (ctors : Std.HashMap String Nat) : Array ConstructorEntry :=
  ctors.fold (init := #[]) fun acc name tag =>
    acc.push { name, tag }

/-- Convert Globals to serializable form -/
def globalsToSerializable (g : Globals) : SerializableGlobals :=
  let pathEntries := g.root.collectPaths #[]
  let seed : Array GlobalDefEntry × Std.HashSet Soma.Core.QualifiedName := (#[], {})
  let (defs, covered) := pathEntries.foldl (init := seed) fun (acc, seen) (ns, displayName, qn) =>
    match g.defs.get? qn with
    | some info => (acc.push { namespacePath := ns, displayName, info }, seen.insert qn)
    | none => (acc, seen)
  let anonymousDefs := g.defs.fold (init := #[]) fun acc qn info =>
    if covered.contains qn then acc else acc.push info
  let inductives := g.inductives.fold (init := #[]) fun acc typeQN info =>
    acc.push { typeQN, info }
  let ctorOwners := g.ctorToInductive.fold (init := #[]) fun acc ctorName inductiveQN =>
    acc.push { ctorName, inductiveQN }
  let wiredIns := g.wiredIn.roles.fold (init := #[]) fun acc role infos =>
    acc.push { role, infos }
  { defs, anonymousDefs, inductives, ctorOwners, wiredIns }

/-- Convert InstanceEnv to serializable form -/
def instanceEnvToSerializable (env : InstanceEnv) : SerializableInstanceEnv :=
  let classes := env.classes.fold (init := #[]) fun acc uid info =>
    acc.push { classId := uid, info }
  let instances := env.instances.fold (init := #[]) fun acc uid insts =>
    acc.push { classId := uid, instances := insts }
  { classes, instances, nextInstanceId := env.nextInstanceId, moduleName := env.moduleName }

/-- Convert AbbrevEnv to serializable form -/
def abbrevEnvToSerializable (env : AbbrevEnv) : SerializableAbbrevEnv :=
  let abbrevs := env.fold (init := #[]) fun acc _qn info => acc.push info
  { abbrevs }

/-- Convert serializable symbols to SymbolEnv -/
def symbolsFromSerializable (entries : Array SymbolEntry) : SymbolEnv :=
  entries.foldl (fun env entry => env.insert entry.symbol entry.type) {}

/-- Convert serializable instances to InstanceMetadata -/
def instanceMetadataFromSerializable (entries : Array InstanceMetadataEntry) : InstanceMetadata :=
  entries.foldl (fun env entry =>
    let instances := entry.instances.map fun e => (e.typeArgs, e.symbol)
    env.insert entry.className instances
  ) {}

/-- Convert serializable constructors to HashMap -/
def constructorsFromSerializable (entries : Array ConstructorEntry) : Std.HashMap String Nat :=
  entries.foldl (fun acc entry => acc.insert entry.name entry.tag) {}

/-- Convert serializable globals to Globals -/
def globalsFromSerializable (sg : SerializableGlobals) : Globals :=
  let g := sg.defs.foldl (fun acc entry =>
    acc.register entry.namespacePath entry.displayName entry.info
  ) Globals.empty
  let g := sg.anonymousDefs.foldl (fun acc info =>
    acc.registerAnonymous info
  ) g
  let inductives := sg.inductives.foldl (fun acc entry => acc.insert entry.typeQN entry.info) {}
  let ctorToInductive := sg.ctorOwners.foldl (fun acc entry => acc.insert entry.ctorName entry.inductiveQN) {}
  let recordFields := sg.inductives.foldl (fun acc entry =>
    if entry.info.fieldNames.isEmpty then acc else acc.insert entry.typeQN entry.info.fieldNames
  ) {}
  let wiredRoles := sg.wiredIns.foldl (fun acc entry => acc.insert entry.role entry.infos) {}
  { g with
    recordFields := recordFields
    inductives := inductives
    ctorToInductive := ctorToInductive
    wiredIn := { roles := wiredRoles } }

/-- Convert serializable instance env to InstanceEnv -/
def instanceEnvFromSerializable (sie : SerializableInstanceEnv) : InstanceEnv :=
  let classes := sie.classes.foldl (fun acc entry => acc.insert entry.classId entry.info) {}
  let instances := sie.instances.foldl (fun acc entry => acc.insert entry.classId entry.instances) {}
  { classes, instances, nextInstanceId := sie.nextInstanceId, moduleName := sie.moduleName }

/-- Convert serializable abbrev env to AbbrevEnv -/
def abbrevEnvFromSerializable (sae : SerializableAbbrevEnv) : AbbrevEnv :=
  sae.abbrevs.foldl (fun env info => env.insert ⟨info.abbrevId⟩ info) {}

/-- Convert ProjectMetadata to ExternalDependency -/
def metadataToExternalDependency (pm : ProjectMetadata) : ExternalDependency :=
  let moduleName := pm.module
  let symbols := symbolsFromSerializable pm.symbols
  let instances := instanceMetadataFromSerializable pm.instances
  let constructors := constructorsFromSerializable pm.constructors
  let globals := globalsFromSerializable pm.globals
  let instanceEnv := instanceEnvFromSerializable pm.instanceEnv
  let abbrevEnv := abbrevEnvFromSerializable pm.abbrevEnv
  {
    name := moduleName
    version := some pm.version
    symbols := ({} : Std.HashMap String SymbolEnv).insert moduleName symbols
    instances := ({} : Std.HashMap String InstanceMetadata).insert moduleName instances
    constructors := constructors
    globals := globals
    instanceEnv := instanceEnv
    abbrevEnv := abbrevEnv
  }

/-- Load metadata from a JSON file -/
def loadMetadataFromJsonFile (path : System.FilePath) : IO (Except String ExternalDependency) := do
  let content ← IO.FS.readFile path
  match Json.decode (α := ProjectMetadata) content with
  | .error e => pure (.error s!"Failed to parse JSON: {e}")
  | .ok pm => do
    -- Accept version 3 (old Lean.Json) and version 4 (Kenosis)
    if pm.version != "3" && pm.version != "4" then
      pure (.error s!"Unsupported metadata version: {pm.version}. Expected version 3 or 4.")
    else
      pure (.ok (metadataToExternalDependency pm))

/-- Load metadata from a file -/
def loadMetadataFromFile (path : System.FilePath) : IO (Except String ExternalDependency) := do
  match path.extension with
  | some "toria" => loadMetadataFromToria path
  | _ => loadMetadataFromJsonFile path

where
  loadMetadataFromToria (path : System.FilePath) : IO (Except String ExternalDependency) := do
    let tmpDir := path.withExtension "extract.tmp"
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

    let metadataPath := extractedDir / "metadata.bin"
    let metadataBytes ← IO.FS.readBinFile metadataPath

    IO.FS.removeDirAll tmpDir |>.catchExceptions fun _ => pure ()

    match Binary.decode metadataBytes with
    | .ok (pm : ProjectMetadata) =>
      if pm.version != "3" && pm.version != "4" then
        pure (.error s!"Unsupported metadata version: {pm.version}. Expected version 3 or 4.")
      else
        pure (.ok (metadataToExternalDependency pm))
    | .error e =>
      pure (.error s!"Failed to decode metadata: {e}")

/-- Load multiple metadata files as external dependencies -/
def loadMetadataFiles (deps : Array (String × System.FilePath)) : IO (Except CheckError (Array ExternalDependency)) := do
  let mut results : Array ExternalDependency := #[]
  for (name, path) in deps do
    match ← loadMetadataFromFile path with
    | .ok dep => results := results.push dep
    | .error e => return .error (.dependencyLoadError name e)
  pure (.ok results)

end Soma.Project.Metadata
