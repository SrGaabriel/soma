import Soma.Project.MetadataLoad
import Soma.Project
import Soma.Project.Check

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
    MetadataLoad.loadMetadataFiles deps

/-- Link checked modules into a single optimized unit -/
def linkModules
    (packageName : String)
    (modules : Array CheckedModule)
    (externalConstructors : Std.HashMap String Nat)
    : IO (String × Std.HashMap String Nat) := do
  IO.println "\n=== Starting link-time optimization phase ==="
  IO.println s!"  Linking {modules.size} modules into package '{packageName}'"

  -- Extract all constructor metadata from modules
  let mut allConstructors : Std.HashMap String Nat := externalConstructors
  for m in modules do
    let ctors := CheckedModule.constructorMetadata m
    for (name, tag) in ctors.toArray do
      allConstructors := allConstructors.insert name tag

  -- TODO: Implement actual code generation
  -- For now, generate placeholder LLVM IR
  let placeholderLLVM := s!"; LLVM IR for package {packageName}\n" ++
    s!"; Modules: {modules.size}\n" ++
    s!"; Constructors: {allConstructors.size}\n"

  IO.println s!"  Collected {allConstructors.size} constructors"
  IO.println "Link-time optimization complete"

  pure (placeholderLLVM, allConstructors)

end Somac.Build
