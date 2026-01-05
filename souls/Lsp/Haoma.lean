/-
  Haoma build tool integration for the Soma LSP server.

  This module provides integration with haoma by calling `haoma metadata`
  to discover project structure and dependencies.
-/
import Lean.Data.Json
import Std.Data.HashMap

namespace Lsp.Haoma

open Lean (Json FromJson ToJson)

/-- Information about a single module in the project -/
structure ModuleInfo where
  /-- Full module name (e.g., "package/subdir/module") -/
  name : String
  /-- Absolute path to the source file -/
  path : String
  /-- Package this module belongs to -/
  package : String
  deriving Repr, Inhabited

instance : FromJson ModuleInfo where
  fromJson? json := do
    let name ← json.getObjValAs? String "name"
    let path ← json.getObjValAs? String "path"
    let package ← json.getObjValAs? String "package"
    return { name, path, package }

/-- Information about a package in the project -/
structure PackageInfo where
  /-- Package name -/
  name : String
  /-- Absolute path to package root -/
  root : String
  /-- Package version -/
  version : String
  /-- Whether this is the root package -/
  isRoot : Bool
  /-- Names of direct dependencies -/
  dependencies : Array String
  deriving Repr, Inhabited

instance : FromJson PackageInfo where
  fromJson? json := do
    let name ← json.getObjValAs? String "name"
    let root ← json.getObjValAs? String "root"
    let version ← json.getObjValAs? String "version"
    let isRoot ← json.getObjValAs? Bool "is_root"
    let dependencies ← json.getObjValAs? (Array String) "dependencies"
    return { name, root, version, isRoot, dependencies }

/-- Complete project metadata from haoma -/
structure ProjectMetadata where
  /-- Whether metadata extraction succeeded -/
  success : Bool
  /-- Error message if extraction failed -/
  error : Option String
  /-- Name of the root package -/
  rootPackage : String
  /-- All packages (root + dependencies) -/
  packages : Array PackageInfo
  /-- All modules across all packages -/
  modules : Array ModuleInfo
  /-- Paths to type metadata files (package name → .meta.json path), only with --full -/
  typeMetadata : Std.HashMap String String := {}
  deriving Repr, Inhabited

instance : FromJson ProjectMetadata where
  fromJson? json := do
    let success ← json.getObjValAs? Bool "success"
    let error := json.getObjValAs? String "error" |>.toOption
    let rootPackage ← json.getObjValAs? String "root_package"
    let packages ← json.getObjValAs? (Array PackageInfo) "packages"
    let modules ← json.getObjValAs? (Array ModuleInfo) "modules"
    -- type_metadata is optional (only present with --full)
    let typeMetadata : Std.HashMap String String := match json.getObjVal? "type_metadata" with
      | .ok (.obj obj) =>
        obj.foldl (init := {}) fun acc k v =>
          match v.getStr? with
          | .ok path => acc.insert k path
          | .error _ => acc
      | _ => {}
    return { success, error, rootPackage, packages, modules, typeMetadata }

/-- Result of loading haoma metadata -/
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
  match Json.parse output.stdout with
  | .error e => return .error s!"Failed to parse haoma output: {e}"
  | .ok json =>
    match FromJson.fromJson? json with
    | .error e => return .error s!"Failed to decode metadata: {e}"
    | .ok (metadata : ProjectMetadata) =>
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
