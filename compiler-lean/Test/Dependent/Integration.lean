/-
  Test.Dependent.Integration - Integration tests for the CQC dependent type system

  These tests run the full dependent type checking pipeline on Soma source code
  from fixture files in Test/fixtures/dependent/*.soma

  Each fixture file starts with a comment like:
    // expect: success
    // expect: error mismatch
    // expect: error unbound

  Tests run with debug=true for detailed logging of the type inference process.
-/

import Soma.Project.Check
import Test.Fixtures

namespace Test.Dependent.Integration

open Soma.Check
open Test.Fixtures

/-! ## Expectation Parsing -/

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

/-! ## Test Running -/

/-- A no-op dependency loader for single-file tests -/
def noDepsLoader (_ : Array (String × System.FilePath)) : IO (Except CheckError (Array ExternalDependency)) :=
  pure (.ok #[])

/-- Run a single test from a fixture file -/
def runDepCheckTest (tc : TestCase) (_debug : Bool := true) : IO TestResult := do
  let expectation := parseExpectation tc.source
  let filePath := s!"Test/fixtures/dependent/{tc.name}"
  let config : ProjectConfig := {
    input := filePath
    name := some tc.name
    deps := #[]
  }
  let result ← checkSingleFile config noDepsLoader

  match expectation with
  | .success =>
    if result.success then
      return .passed
    else
      let diagErrors := result.diagnostics.filter (·.severity == .error)
        |>.map (·.message) |>.toList
      return .failed s!"Expected success but got errors:\n  {String.intercalate "\n  " diagErrors}"

  | .error expectedSubstr =>
    if result.success then
      return .failed "Expected error but type checking succeeded"
    else
      match expectedSubstr with
      | some substr =>
        let diagMsgs := result.diagnostics.filter (·.severity == .error) |>.map (·.message)
        -- Check if any error message contains the expected substring
        if diagMsgs.any (fun msg => msg.toSlice.contains substr) then
          return .passed
        else
          return .failed s!"Expected error containing '{substr}' but got: {diagMsgs.toList}"
      | none =>
        return .passed  -- Just expected some error, got one

/-- Run all tests from the dependent fixtures directory -/
def runFromFixtures (debug : Bool := true) : IO TestRunner := do
  IO.println "=== Dependent Type Integration Tests (from fixtures) ==="
  let cases ← loadAllTestCases "dependent"
  let mut runner := TestRunner.init

  for tc in cases do
    let result ← runDepCheckTest tc debug
    match result with
    | .passed => IO.println s!"  [PASS] {tc.name}"
    | .failed msg => IO.println s!"  [FAIL] {tc.name}: {msg}"
    | .skipped reason => IO.println s!"  [SKIP] {tc.name}: {reason}"
    runner := runner.record tc.name result

  return runner

/-! ## Main Entry Point -/

def run : IO TestRunner := do
  -- Run with debug=true for verbose output during development
  let runner ← runFromFixtures (debug := true)

  IO.println ""
  runner.printSummary "Dependent Integration"
  IO.println ""
  return runner

end Test.Dependent.Integration
