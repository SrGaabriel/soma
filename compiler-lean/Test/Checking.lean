/-
  Type Checking Tests (End-to-End)

  These tests run complete Soma programs through the full compilation pipeline:
  Source -> Lex -> Parse -> Lower -> Metal -> Type Inference

  Test fixtures are in Test/fixtures/checking/*.soma
  Each file starts with a comment like:
    // expect: success
    // expect: error mismatch
-/

import Soma.Syntax
import Soma.Metal
import Soma.Infer
import Soma.Infer.Module
import Test.Fixtures

namespace Test.Checking

open Soma.Syntax
open Soma.Infer
open Soma.Typing
open Soma.Metal (UntypedModule)
open Test.Fixtures

/-- Expectation parsed from fixture comment -/
inductive Expectation where
  | success : Expectation
  | error (substring : Option String) : Expectation
  deriving Repr

/-- Parse expectation from first line of source -/
def parseExpectation (source : String) : Expectation :=
  let firstLine := source.takeWhile (· != '\n')
  if firstLine.startsWith "// expect: success" then
    .success
  else if firstLine.startsWith "// expect: error" then
    let rest := firstLine.drop "// expect: error".length |>.trim
    if rest.isEmpty then .error none else .error (some rest)
  else
    .success  -- Default to success if no expectation comment

/-- Result of running the full pipeline on source code -/
structure CheckResult where
  lexDiags : Diagnostics
  parseDiags : Diagnostics
  astLowerDiags : Diagnostics
  metalLowerDiags : Diagnostics
  inferErrors : Array InferError

namespace CheckResult

def allDiagnostics (r : CheckResult) : Diagnostics :=
  r.lexDiags ++ r.parseDiags ++ r.astLowerDiags ++ r.metalLowerDiags

def allErrors (r : CheckResult) : Diagnostics :=
  r.allDiagnostics.filter (·.severity == .error)

def hasErrors (r : CheckResult) : Bool :=
  !r.allErrors.isEmpty || !r.inferErrors.isEmpty

def isSuccess (r : CheckResult) : Bool :=
  !r.hasErrors

def errorMessages (r : CheckResult) : Array String :=
  r.allErrors.map (·.message) ++ r.inferErrors.map (·.toDiagnostic.message)

end CheckResult

/-- Run the full pipeline on source code -/
def runCheck (source : String) (moduleName : String := "Test") : CheckResult := Id.run do
  let fileId : FileId := ⟨0⟩
  let sourceFile := SourceFile.create fileId "test.soma" source

  -- Phase 1: Lexing
  let (tokens, lexDiags) := lexCode sourceFile

  -- Phase 2: Parsing
  let (cst, parseDiags) := Parse.parseSourceFile.run' tokens sourceFile

  -- Phase 3: Lower CST to AST
  let (ast, astLowerDiags) := lower cst moduleName

  -- Phase 4: Lower AST to Metal IR
  let lowerResult := Soma.Metal.Lower.lower ast
  let metalLowerDiags := Soma.Metal.Lower.LowerError.toDiagnostics lowerResult.errors

  -- Phase 5: Type inference
  let supply := Soma.UniqueSupply.initial "Test"
  let (typeEnv, supply) := Soma.Infer.buildTypeEnvFromModule lowerResult.module #[] supply
  let instanceEnv := Soma.Infer.buildInstanceEnvFromModule lowerResult.module InstanceEnv.empty typeEnv
  let inferCtx : InferContext := {
    typeEnv := typeEnv
    instanceEnv := instanceEnv
    currentFunction := none
  }
  let _ := supply -- suppress unused warning
  let inferResult := Soma.Infer.inferModule lowerResult.module inferCtx

  return {
    lexDiags := lexDiags
    parseDiags := parseDiags
    astLowerDiags := astLowerDiags
    metalLowerDiags := metalLowerDiags
    inferErrors := inferResult.errors
  }

/-- Run a single checking test from a fixture -/
def runCheckingTest (tc : TestCase) : IO TestResult := do
  let expectation := parseExpectation tc.source
  let result := runCheck tc.source

  match expectation with
  | .success =>
    if result.isSuccess then
      return .passed
    else
      let errors := result.errorMessages
      return .failed s!"Expected success but got errors: {errors}"

  | .error expectedSubstr =>
    if result.hasErrors then
      match expectedSubstr with
      | some substr =>
        let msgs := result.errorMessages
        if msgs.any (fun msg => msg.toSlice.contains substr) then
          return .passed
        else
          return .failed s!"Expected error containing '{substr}' but got: {msgs}"
      | none =>
        return .passed  -- Just expected some error, got one
    else
      return .failed "Expected error but compilation succeeded"

/-- Run all checking tests from fixtures -/
def runFromFixtures : IO TestRunner := do
  IO.println "=== Checking Tests (from fixtures) ==="
  let cases ← loadAllTestCases "checking"
  let mut runner := TestRunner.init
  for tc in cases do
    let result ← runCheckingTest tc
    match result with
    | .passed => IO.println s!"  [PASS] {tc.name}"
    | .failed msg => IO.println s!"  [FAIL] {tc.name}: {msg}"
    | .skipped reason => IO.println s!"  [SKIP] {tc.name}: {reason}"
    runner := runner.record tc.name result
  return runner

/-- Main entry point for checking tests -/
def run : IO Unit := do
  let runner ← runFromFixtures
  runner.printSummary "Checking Summary"
  IO.println ""

end Test.Checking
