/-
  Haoma build tool integration for the Soma LSP server.

  This module provides integration with haoma by calling `haoma metadata`
  to discover project structure and dependencies.
-/
import Kenosis
import Std.Data.HashMap

namespace Lsp.Haoma

open Kenosis

/-- Information about a single module in the project -/
structure ModuleInfo where
  /-- Full module name (e.g., "package/subdir/module") -/
  name : String
  /-- Absolute path to the source file -/
  path : String
  /-- Package this module belongs to -/
  package : String
  deriving Repr, Inhabited, Deserialize

/-- Information about a package in the project -/
structure PackageInfo where
  /-- Package name -/
  name : String
  /-- Absolute path to package root -/
  root : String
  /-- Package version -/
  version : String
  /-- Whether this is the root package -/
  is_root : Bool
  /-- Names of direct dependencies -/
  dependencies : Array String
  deriving Repr, Inhabited, Deserialize

/-- Complete project metadata from haoma -/
structure ProjectMetadata where
  /-- Whether metadata extraction succeeded -/
  success : Bool
  /-- Error message if extraction failed -/
  error : Option String
  /-- Name of the root package -/
  root_package : String
  /-- All packages (root + dependencies) -/
  packages : Array PackageInfo
  /-- All modules across all packages -/
  modules : Array ModuleInfo
  /-- Paths to type metadata files (package name → .meta.json path), only with --full -/
  type_metadata : Std.HashMap String String := {}
  deriving Repr, Inhabited

/-- Deserialize ProjectMetadata from JSON, handling optional type_metadata field -/
def deserializeProjectMetadata (input : String) : Except Json.JsonError ProjectMetadata := do
  let value ← Json.JsonReader.run input Json.parseValue
  let success ← getFieldValue value "success" getBoolValue
  let error ← getOptFieldValue value "error" getStrValue
  let root_package ← getFieldValue value "root_package" getStrValue
  let packages ← getFieldValue value "packages" (getArrayValue deserializePackageInfo)
  let modules ← getFieldValue value "modules" (getArrayValue deserializeModuleInfo)
  -- type_metadata is optional (only present with --full)
  let type_metadata : Std.HashMap String String := match getFieldRaw value "type_metadata" with
    | some (.obj metaFields) =>
      metaFields.foldl (init := {}) fun acc (k, v) =>
        match v with
        | .str path => acc.insert k path
        | _ => acc
    | _ => {}
  return { success, error, root_package, packages, modules, type_metadata }
where
  getFieldRaw (v : Json.JsonValue) (name : String) : Option Json.JsonValue :=
    match v with
    | .obj fields => fields.find? (fun (k, _) => k == name) |>.map (·.2)
    | _ => none
  getFieldValue {α : Type} (v : Json.JsonValue) (name : String) (decode : Json.JsonValue → Except Json.JsonError α) : Except Json.JsonError α := do
    match getFieldRaw v name with
    | some fieldVal => decode fieldVal
    | none => .error (.custom s!"missing field '{name}'" 0)
  getOptFieldValue {α : Type} (v : Json.JsonValue) (name : String) (decode : Json.JsonValue → Except Json.JsonError α) : Except Json.JsonError (Option α) := do
    match getFieldRaw v name with
    | some .null => return none
    | some fieldVal => return some (← decode fieldVal)
    | none => return none
  getBoolValue : Json.JsonValue → Except Json.JsonError Bool
    | .bool b => return b
    | _ => .error (.custom "expected boolean" 0)
  getStrValue : Json.JsonValue → Except Json.JsonError String
    | .str s => return s
    | _ => .error (.custom "expected string" 0)
  getArrayValue {α : Type} (decodeElem : Json.JsonValue → Except Json.JsonError α) : Json.JsonValue → Except Json.JsonError (Array α)
    | .arr xs => xs.toArray.mapM decodeElem
    | _ => .error (.custom "expected array" 0)
  deserializeModuleInfo (v : Json.JsonValue) : Except Json.JsonError ModuleInfo := do
    let name ← getFieldValue v "name" getStrValue
    let path ← getFieldValue v "path" getStrValue
    let package ← getFieldValue v "package" getStrValue
    return { name, path, package }
  deserializePackageInfo (v : Json.JsonValue) : Except Json.JsonError PackageInfo := do
    let name ← getFieldValue v "name" getStrValue
    let root ← getFieldValue v "root" getStrValue
    let version ← getFieldValue v "version" getStrValue
    let is_root ← getFieldValue v "is_root" getBoolValue
    let dependencies ← getFieldValue v "dependencies" (getArrayValue getStrValue)
    return { name, root, version, is_root, dependencies }data -/
inductive LoadResult
  /-- Successfully loaded project metadata -/
  | ok (metadata : ProjectMetadata)
  /-- Not a haoma project (no haoma.kdl found) -/
  | notHaomaProject
  /-- Failed to load metadata -/
  | error (message : String)
  deriving Repr, Inhabited

/-- Check if a directory contains a haoma.kdl file -/
def isHaomaProject (path : System.FilePath) : IO Bool := do
  let manifestPath := path / "haoma.kdl"
  manifestPath.pathExists

/-- Find the haoma project root by walking up from a file path -/
def findProjectRoot (filePath : System.FilePath) : IO (Option System.FilePath) := do
  let mut current := filePath
  -- If it's a file, start from its parent directory
  if ← current.isDir then
    pure ()
  else
    current := current.parent.getD current

  -- Walk up the directory tree looking for haoma.kdl
  for _ in [:100] do  -- Limit iterations to prevent infinite loops
    if ← isHaomaProject current then
      return some current
    match current.parent with
    | some parent =>
      if parent == current then
        return none  -- Reached filesystem root
      current := parent
    | none => return none

  return none

/-- Run haoma metadata command and parse the output -/
def loadMetadata (projectRoot : System.FilePath) (full : Bool := false) : IO LoadResult := do
  -- First verify this is a haoma project
  if !(← isHaomaProject projectRoot) then
    return .notHaomaProject

  -- Run haoma metadata command
  let args := if full then
    #["metadata", "--path", projectRoot.toString, "--full"]
  else
    #["metadata", "--path", projectRoot.toString]

  let output ← IO.Process.output {
    cmd := "haoma"
    args := args
    cwd := some projectRoot
  }

  -- Check for command execution errors
  if output.exitCode != 0 then
    return .error s!"haoma metadata failed (exit code {output.exitCode}): {output.stderr}"

  -- Parse JSON output
  match deserializeProjectMetadata output.stdout with
  | .error e => return .error s!"Failed to parse haoma output: {e}"
  | .ok metadata =>
    if metadata.success then
      return .ok metadata
    else
      return .error (metadata.error.getD "Unknown error")

/-- Run haoma metadata --full to get type metadata paths -/
def loadMetadataFull (projectRoot : System.FilePath) : IO LoadResult :=
  loadMetadata projectRoot (full := true)

/-- Load metadata for a project containing the given file -/
def loadMetadataForFile (filePath : System.FilePath) : IO LoadResult := do
  match ← findProjectRoot filePath with
  | none => return .notHaomaProject
  | some root => loadMetadata root

/-- Recursively scan a directory for haoma.kdl files -/
partial def scanForProjects (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut results : Array System.FilePath := #[]

  -- Check if this directory has haoma.kdl
  if ← isHaomaProject root then
    results := results.push root

  -- Scan subdirectories
  let entries ← root.readDir
  for entry in entries do
    let path := entry.path
    -- Skip hidden directories and common non-project directories
    let name := entry.fileName
    if name.startsWith "." || name == "node_modules" || name == "target" || name == "dist-newstyle" then
      continue
    if ← path.isDir then
      let subResults ← scanForProjects path
      results := results ++ subResults

  return results

/-- Discover all haoma projects in a workspace -/
def discoverProjects (workspaceRoot : System.FilePath) : IO (Array System.FilePath) := do
  scanForProjects workspaceRoot

end Lsp.Haoma
