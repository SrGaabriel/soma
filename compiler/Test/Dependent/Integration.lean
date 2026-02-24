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

open Soma.Project.Check
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
    let rest := firstLine.drop "// expect: error".length |>.trimAscii |>.copy
    if rest.isEmpty then .error none else .error (some rest)
  else
    .success  -- Default to success if no expectation comment

/-! ## Test Running -/

/-- Path to the shared fixture prelude for dependent tests -/
def dependentPrimPath : System.FilePath := "Test/fixtures/shared/prim.soma"

/-- Build a temporary source file that prepends shared fixture prim definitions -/
def writeTempDependentFixture (fileName : String) (source : String) : IO System.FilePath := do
  let primSource ← IO.FS.readFile dependentPrimPath
  let timestamp ← IO.monoMsNow
  let tempDir : System.FilePath := ".lake/test-dependent"
  IO.FS.createDirAll tempDir
  let tempPath := tempDir / s!"{fileName}-{timestamp}.soma"
  let merged := primSource ++ "\n\n" ++ source
  IO.FS.writeFile tempPath merged
  pure tempPath

/-- A no-op dependency loader for single-file tests -/
def noDepsLoader (_ : Array (String × System.FilePath)) : IO (Except CheckError (Array ExternalDependency)) :=
  pure (.ok #[])

/-- Run a single test from a fixture file -/
def runDepCheckTest (tc : TestCase) (_debug : Bool := true) : IO TestResult := do
  let expectation := parseExpectation tc.source
  let tempPath ← writeTempDependentFixture tc.name tc.source
  let config : ProjectConfig := {
    input := tempPath
    name := some tc.name
    deps := #[]
  }
  let result ← checkSingleFile config noDepsLoader

  try
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
          if diagMsgs.any (fun msg => msg.toSlice.contains substr) then
            return .passed
          else
            return .failed s!"Expected error containing '{substr}' but got: {diagMsgs.toList}"
        | none =>
          return .passed
  finally
    IO.FS.removeFile tempPath |>.catchExceptions fun _ => pure ()

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
