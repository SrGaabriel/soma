import Soma.Project.Metadata
import Soma.Project
import Soma.Project.Check
import Soma.Metal.LambdaLift
import Somac.Circuit
import Somac.Alloy
import Somac.Alloy.Merge
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
  let alloyModules : Array (String × Alloy.Module) := modules.map fun cm =>
    (cm.name, lowerToAlloy cm mergedGlobals)

  IO.println s!"  Generated {alloyModules.size} Alloy module(s)"

  -- Merge all Alloy modules into one
  IO.println "  Merging modules..."
  let merged := Alloy.Merge.merge alloyModules packageName

  IO.println s!"  Merged module has {merged.funcs.size} function(s)"

  -- Monomorphize
  IO.println "  Monomorphizing..."
  let mono := Alloy.Monomorphize.monomorphize merged

  IO.println s!"  Monomorphized module has {mono.funcs.size} function(s)"

  -- Generate LLVM IR
  IO.println "  Generating LLVM IR..."
  let llvmIR := Llvm.codegenToString mono

  IO.println "Compilation phase complete"

  pure { llvmIR, constructors := allConstructors, alloyModules }

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
