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
        let diagErrors := result.diagnostics.filter (fun d => d.severity.level == .error)
          |>.map (fun d =>
            let labels := (d.primary :: d.secondary).filterMap (·.message)
            let labelStr := if labels.isEmpty then "" else "\n    > " ++ String.intercalate "\n    > " labels
            s!"{d.message}{labelStr}") |>.toList
        return .failed s!"Expected success but got errors:\n  {String.intercalate "\n  " diagErrors}"

    | .error expectedSubstr =>
      if result.success then
        return .failed "Expected error but type checking succeeded"
      else
        match expectedSubstr with
        | some substr =>
          let diagMsgs := result.diagnostics.filter (·.severity.level == .error) |>.map (·.message)
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

/-- Walk a Value and return true if any neutral head is/contains an unsolved meta -/
partial def valueContainsMetaHead (v : Soma.Core.Value) : Bool :=
  match v with
  | .vNeutral ty neu =>
    let headIsMeta := match neu.head with
      | .hMeta _ => true
      | .hCase scruts motive _ =>
        scruts.any valueContainsMetaHead || valueContainsMetaHead motive
      | _ => false
    headIsMeta
      || valueContainsMetaHead ty
      || neu.spine.any fun
        | .eApp arg => valueContainsMetaHead arg
        | .eField _ => false
  | .vPi _ _ _ dom cod =>
    valueContainsMetaHead dom || match cod with
      | .const _ v => valueContainsMetaHead v
      | .term _ _ _ => false
  | .vLam _ body => match body with
    | .const _ v => valueContainsMetaHead v
    | .term _ _ _ => false
  | .vRowExtend l ft t =>
    valueContainsMetaHead l || valueContainsMetaHead ft || valueContainsMetaHead t
  | .vRecord row => valueContainsMetaHead row
  | .vVariant row => valueContainsMetaHead row
  | .vRecordVal fields => fields.any (fun (_, v) => valueContainsMetaHead v)
  | .vDataType _ params => params.any valueContainsMetaHead
  | .vConstructor _ _ args rty =>
    args.any valueContainsMetaHead || valueContainsMetaHead rty
  | _ => false

/-- Verify that the stored type of `defName` in `result` is concrete -/
def checkStoredTypeConcrete (result : ProjectResult) (defName : String) : Option String := Id.run do
  if !result.success then return some s!"project failed to check"
  for m in result.checkedModules do
    for (_qn, info) in m.globals.defs.toList do
      if info.name.display == defName then
        if valueContainsMetaHead info.type then
          return some s!"stored type for `{defName}` still contains an unsolved meta: {info.type}"
        else
          return none
  return some s!"symbol `{defName}` not found in any checked module"

def testTraitMethodSignatureConcrete : IO TestResult := do
  let fixturePath : System.FilePath := "Test/fixtures/dependent/trait_method_in_signature.soma"
  let source ← IO.FS.readFile fixturePath
  let tempPath ← writeTempDependentFixture "trait_method_in_signature" source
  let config : ProjectConfig := {
    input := tempPath
    name := some "trait_method_in_signature"
    deps := #[]
  }
  try
    let result ← checkSingleFile config noDepsLoader
    match checkStoredTypeConcrete result "succ_greater_than_zero" with
    | none => return .passed
    | some msg => return .failed msg
  finally
    IO.FS.removeFile tempPath |>.catchExceptions fun _ => pure ()

def runInvariantTests : IO TestRunner := do
  IO.println "  === Stored-Type Invariants ==="
  let mut runner := TestRunner.init
  runner := runner.record "trait_method_signature_concrete"
    (← testTraitMethodSignatureConcrete)
  return runner

/-! ## Main Entry Point -/

def run : IO TestRunner := do
  -- Run with debug=true for verbose output during development
  let runner ← runFromFixtures (debug := true)
  let invariants ← runInvariantTests

  IO.println ""
  runner.printSummary "Dependent Integration"
  invariants.printSummary "Stored-Type Invariants"
  IO.println ""
  return runner.merge invariants

end Test.Dependent.Integration
