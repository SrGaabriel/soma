import Std.Data.HashSet
import Soma.Syntax
import Soma.Metal
import Soma.Metal.Lower.Decl
import Soma.Infer
import Soma.Unique

namespace Soma.Check

open Std (HashSet)
open Soma.Syntax
open Soma.Metal.Lower (IncrementalLowerResult lowerModuleFresh lowerModuleWithExternals lowerModuleIncremental GlobalEnv)
open Soma.Infer
open Soma.Typing
open Soma (UniqueSupply)

/-! ## Helper functions -/

/-- Derive module name from file path -/
def moduleNameFromPath (filePath : String) : String :=
  let parts := filePath.splitOn "/"
  let fileName := parts.getLast!
  let nameParts := fileName.splitOn "."
  if nameParts.isEmpty then fileName else nameParts.head!

/-- Create a file ID from path -/
def fileIdFromPath (filePath : String) : FileId :=
  ⟨filePath.hash.toNat⟩

/-! ## Phase Results

Each phase returns its output plus diagnostics. We use a simple pattern:
the result is always produced (phases are infallible), diagnostics are collected.
-/

/-- Result of parsing -/
structure ParseResult where
  sourceFile : SourceFile
  tree : ParsedTree
  diagnostics : Diagnostics

/-- Result of CST → AST lowering -/
structure LowerResult where
  ast : Syntax.Module
  diagnostics : Diagnostics

/-- Result of AST → Metal IR lowering -/
structure MetalResult where
  module : Metal.UntypedModule
  result : IncrementalLowerResult  -- Contains caches for incremental updates
  diagnostics : Diagnostics

/-- Result of type inference -/
structure InferResult where
  module : Metal.Module
  typeEnv : TypeEnv
  instanceEnv : InstanceEnv
  diagnostics : Diagnostics

/-- Phase 1+2: Parse source code (lex + parse combined) -/
def parse (filePath : String) (content : String) : ParseResult :=
  let sourceFile := SourceFile.create (fileIdFromPath filePath) filePath content
  let (tree, diags) := parseToTree sourceFile
  { sourceFile, tree, diagnostics := diags }

/-- Phase 2b: Incremental reparse -/
def reparse (oldTree : ParsedTree) (filePath : String) (content : String)
    : ParseResult × HashSet NodeId :=
  let sourceFile := SourceFile.create (fileIdFromPath filePath) filePath content
  let (tree, diags) := reparseToTree oldTree sourceFile
  let oldIds := oldTree.red.idToIdx
  let newIds := tree.red.idToIdx
  let changedIds := newIds.fold (init := {}) fun acc nodeId _ =>
    if oldIds.contains nodeId then acc else acc.insert nodeId
  ({ sourceFile, tree, diagnostics := diags }, changedIds)

/-- Phase 3: Lower CST to AST -/
def lower (tree : ParsedTree) (moduleName : String) : LowerResult :=
  let (ast, diags) := Syntax.lower tree moduleName
  { ast, diagnostics := diags }

/-- Phase 4: Lower AST to Metal IR -/
def metal (ast : Syntax.Module) : MetalResult :=
  let result := lowerModuleFresh ast
  let diags := Metal.Lower.LowerError.toDiagnostics result.errors
  { module := result.module, result, diagnostics := diags }

/-- Phase 4 with external symbols: Lower AST to Metal IR with pre-populated GlobalEnv -/
def metalWithExternals (ast : Syntax.Module) (initialEnv : Metal.Lower.GlobalEnv) : MetalResult :=
  let result := lowerModuleWithExternals ast initialEnv
  let diags := Metal.Lower.LowerError.toDiagnostics result.errors
  { module := result.module, result, diagnostics := diags }

/-- Phase 4b: Incremental Metal lowering -/
def metalIncremental (ast : Syntax.Module) (changedNames : Array String)
    (oldResult : IncrementalLowerResult) : MetalResult :=
  let result := lowerModuleIncremental ast changedNames oldResult
  let diags := Metal.Lower.LowerError.toDiagnostics result.errors
  { module := result.module, result, diagnostics := diags }

/-- Phase 5: Type inference -/
def infer (module : Metal.UntypedModule) (typeEnv : TypeEnv) (instanceEnv : InstanceEnv)
    : InferResult :=
  let ctx : InferContext := { typeEnv, instanceEnv, currentFunction := none }
  let result := inferModule module ctx
  let diags := InferErrors.toDiagnostics result.errors
  { module := result.module, typeEnv, instanceEnv, diagnostics := diags }

/-- Build type environment from a Metal module -/
def buildTypeEnv (module : Metal.UntypedModule)
    (externalFns : Array (String × FunctionInfo) := #[])
    (supply : UniqueSupply) : TypeEnv × UniqueSupply :=
  buildTypeEnvFromModule module externalFns supply

/-- Build instance environment from a Metal module -/
def buildInstanceEnv (module : Metal.UntypedModule)
    (externalInstances : InstanceEnv := InstanceEnv.empty)
    (typeEnv : TypeEnv) : InstanceEnv :=
  buildInstanceEnvFromModule module externalInstances typeEnv

/-- Configuration for the full pipeline -/
structure Config where
  /-- External functions from dependencies -/
  externalFunctions : Array (String × FunctionInfo) := #[]
  /-- External instances from dependencies -/
  externalInstances : InstanceEnv := InstanceEnv.empty
  /-- Unique supply for fresh names -/
  supply : UniqueSupply
  /-- Whether to stop after frontend errors -/
  stopOnFrontendErrors : Bool := false

/-- Full pipeline result -/
structure FullResult where
  moduleName : String
  sourceFile : SourceFile
  parsedTree : ParsedTree
  ast : Syntax.Module
  metalModule : Metal.UntypedModule
  metalResult : IncrementalLowerResult
  typedModule : Metal.Module
  typeEnv : TypeEnv
  instanceEnv : InstanceEnv
  diagnostics : Diagnostics

namespace FullResult

def hasErrors (r : FullResult) : Bool := r.diagnostics.hasErrors
def errorCount (r : FullResult) : Nat := r.diagnostics.filter (·.severity == .error) |>.size

end FullResult

/-- Run the full pipeline: parse → lower → metal → infer -/
def full (filePath : String) (content : String) (config : Config) : FullResult := Id.run do
  let moduleName := moduleNameFromPath filePath

  -- Parse
  let parseRes := parse filePath content

  -- Lower CST → AST
  let lowerRes := lower parseRes.tree moduleName
  let frontendDiags := parseRes.diagnostics ++ lowerRes.diagnostics

  -- Metal lowering
  let metalRes := metal lowerRes.ast

  -- Check for early exit on frontend errors
  if config.stopOnFrontendErrors && frontendDiags.hasErrors then
    let (typeEnv, _) := buildTypeEnv metalRes.module config.externalFunctions config.supply
    let instanceEnv := buildInstanceEnv metalRes.module config.externalInstances typeEnv
    return {
      moduleName, sourceFile := parseRes.sourceFile, parsedTree := parseRes.tree
      ast := lowerRes.ast
      metalModule := metalRes.module, metalResult := metalRes.result
      typedModule := { name := moduleName, functions := #[], types := #[], typeClasses := #[], instances := #[] }
      typeEnv, instanceEnv
      diagnostics := frontendDiags ++ metalRes.diagnostics
    }

  -- Build environments
  let (typeEnv, _) := buildTypeEnv metalRes.module config.externalFunctions config.supply
  let instanceEnv := buildInstanceEnv metalRes.module config.externalInstances typeEnv

  -- Type inference
  let inferRes := infer metalRes.module typeEnv instanceEnv

  let allDiags := frontendDiags ++ metalRes.diagnostics ++ inferRes.diagnostics

  return {
    moduleName, sourceFile := parseRes.sourceFile, parsedTree := parseRes.tree
    ast := lowerRes.ast
    metalModule := metalRes.module, metalResult := metalRes.result
    typedModule := inferRes.module
    typeEnv := inferRes.typeEnv, instanceEnv := inferRes.instanceEnv
    diagnostics := allDiags
  }

/-- Simple full pipeline with default config -/
def fullSimple (filePath : String) (content : String) : FullResult :=
  let moduleName := moduleNameFromPath filePath
  full filePath content { supply := UniqueSupply.initial moduleName }

/-- Run full pipeline from file -/
def fullFromFile (filePath : String) (config : Config) : IO FullResult := do
  let content ← IO.FS.readFile filePath
  pure (full filePath content config)

/-- Simple full pipeline from file -/
def fullFromFileSimple (filePath : String) : IO FullResult := do
  let content ← IO.FS.readFile filePath
  pure (fullSimple filePath content)

/-- Parse only -/
def parseOnly (filePath : String) (content : String) : ParseResult :=
  parse filePath content

/-- Parse + lower to AST -/
def toAst (filePath : String) (content : String) : ParseResult × LowerResult :=
  let parseRes := parse filePath content
  let moduleName := moduleNameFromPath filePath
  let lowerRes := lower parseRes.tree moduleName
  (parseRes, lowerRes)

/-- Parse + lower to Metal IR -/
def toMetal (filePath : String) (content : String) : ParseResult × LowerResult × MetalResult :=
  let (parseRes, lowerRes) := toAst filePath content
  let metalRes := metal lowerRes.ast
  (parseRes, lowerRes, metalRes)

/-- Check if diagnostics have errors -/
def hasErrors (diags : Diagnostics) : Bool := diags.hasErrors

/-- Combine diagnostics from multiple sources -/
def combineDiags (sources : Array Diagnostics) : Diagnostics :=
  sources.foldl (· ++ ·) #[]

end Soma.Check
