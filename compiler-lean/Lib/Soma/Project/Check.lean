/-
  Unified type-checking pipeline for Soma source files.

  This module provides a common interface used by:
  - The LSP server (for real-time diagnostics)
  - The `somac check` command (for standalone type-checking)
  - The build pipeline (as part of compilation)

  Pipeline: Source → Lex → Parse → CST Lower → Metal Lower → Type Infer
  All phases are infallible and collect errors.
-/

import Soma.Syntax
import Soma.Metal
import Soma.Infer
import Soma.Unique
import Soma.Project.Symbol

namespace Soma.Project.Check

open Soma.Syntax
open Soma.Metal
open Soma.Infer
open Soma.Typing
open Soma (UniqueSupply)

/-- Result of checking a single source file -/
structure CheckResult where
  /-- Module name derived from file path -/
  moduleName : String
  /-- Source file object for error rendering -/
  sourceFile : SourceFile
  /-- The parsed CST -/
  cst : SyntaxNode
  /-- The lowered AST (if frontend succeeded) -/
  ast : Option Syntax.Module
  /-- The Metal IR module (if lowering succeeded) -/
  metalModule : Option UntypedModule
  /-- The typed Metal module (if inference succeeded) -/
  typedModule : Option Metal.Module
  /-- All collected diagnostics -/
  diagnostics : Diagnostics

namespace CheckResult

/-- Check if the result has any errors -/
def hasErrors (r : CheckResult) : Bool :=
  r.diagnostics.hasErrors

/-- Get only error diagnostics -/
def errors (r : CheckResult) : Diagnostics :=
  r.diagnostics.filter (·.severity == .error)

/-- Get error count -/
def errorCount (r : CheckResult) : Nat :=
  r.errors.size

/-- Check if frontend (lex/parse/lower) succeeded -/
def frontendSucceeded (r : CheckResult) : Bool :=
  r.ast.isSome

/-- Check if Metal lowering succeeded -/
def metalSucceeded (r : CheckResult) : Bool :=
  r.metalModule.isSome

/-- Check if type inference completed -/
def inferenceCompleted (r : CheckResult) : Bool :=
  r.typedModule.isSome

end CheckResult

/-- Configuration for the check pipeline -/
structure CheckConfig where
  /-- External functions available from dependencies -/
  externalFunctions : Array (String × FunctionInfo) := #[]
  /-- External instance environment from dependencies -/
  externalInstances : Infer.InstanceEnv := Infer.InstanceEnv.empty
  /-- Initial unique supply (for fresh type variables) -/
  supply : UniqueSupply
  /-- Whether to stop at frontend errors (vs continuing to Metal) -/
  stopOnFrontendErrors : Bool := true

/-- Derive module name from file path -/
def moduleNameFromPath (filePath : String) : String :=
  let parts := filePath.splitOn "/"
  let fileName := parts.getLast!
  let nameParts := fileName.splitOn "."
  if nameParts.isEmpty then fileName
  else nameParts.head!

/-- Create a file ID from path (using hash) -/
def fileIdFromPath (filePath : String) : FileId :=
  ⟨filePath.hash.toNat⟩

/-- Check a source file with the given content.
    This is the core pipeline used by LSP, check command, and build. -/
def checkSource (filePath : String) (content : String) (config : CheckConfig) : CheckResult := Id.run do
  let moduleName := moduleNameFromPath filePath
  let fileId := fileIdFromPath filePath

  -- Phase 1: Create source file with line information
  let sourceFile := SourceFile.create fileId filePath content

  -- Phase 2: Lexing (infallible)
  let (tokens, lexDiags) := lexCode sourceFile

  -- Phase 3: Parsing (infallible - always produces CST)
  let (cst, parseDiags) := Parse.parseSourceFile.run' tokens sourceFile

  -- Phase 4: Lower CST to AST (infallible, collects errors)
  let (ast, astLowerDiags) := lower cst moduleName

  let frontendDiags := lexDiags ++ parseDiags ++ astLowerDiags

  -- If frontend has errors and config says to stop, return early
  if config.stopOnFrontendErrors && frontendDiags.hasErrors then
    return {
      moduleName := moduleName
      sourceFile := sourceFile
      cst := cst
      ast := some ast
      metalModule := none
      typedModule := none
      diagnostics := frontendDiags
    }

  -- Phase 5: Lower AST to Metal IR (infallible, collects errors)
  let lowerResult := Metal.Lower.lower ast
  let metalLowerDiags := Metal.Lower.LowerError.toDiagnostics lowerResult.errors

  -- Phase 6: Type inference on Metal module (infallible, collects errors)
  let (typeEnv, _supply) := Infer.buildTypeEnvFromModule lowerResult.module config.externalFunctions config.supply
  let instanceEnv := Infer.buildInstanceEnvFromModule lowerResult.module config.externalInstances typeEnv

  let inferCtx : InferContext := {
    typeEnv := typeEnv
    instanceEnv := instanceEnv
    currentFunction := none
  }

  let inferResult := Infer.inferModule lowerResult.module inferCtx
  let inferDiags := InferErrors.toDiagnostics inferResult.errors

  -- Combine all diagnostics
  let allDiags := frontendDiags ++ metalLowerDiags ++ inferDiags

  return {
    moduleName := moduleName
    sourceFile := sourceFile
    cst := cst
    ast := some ast
    metalModule := some lowerResult.module
    typedModule := some inferResult.module
    diagnostics := allDiags
  }

/-- Check a source file with default configuration (no external dependencies) -/
def checkSourceSimple (filePath : String) (content : String) : CheckResult :=
  let moduleName := moduleNameFromPath filePath
  let config : CheckConfig := {
    supply := UniqueSupply.initial moduleName
  }
  checkSource filePath content config

/-- Check a source file, reading content from disk -/
def checkFile (filePath : String) (config : CheckConfig) : IO CheckResult := do
  let content ← IO.FS.readFile filePath
  pure (checkSource filePath content config)

/-- Check a source file with default configuration, reading from disk -/
def checkFileSimple (filePath : String) : IO CheckResult := do
  let content ← IO.FS.readFile filePath
  pure (checkSourceSimple filePath content)

end Soma.Project.Check
