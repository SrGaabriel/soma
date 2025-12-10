namespace Test.Fixtures

/-- Get the path to the Test/fixtures directory -/
def fixturesDir : System.FilePath := "Test/fixtures"

/-- Get the path to a specific fixture category -/
def categoryDir (category : String) : System.FilePath :=
  fixturesDir / category

/-- Read a fixture file's contents -/
def readFixture (category : String) (name : String) : IO String := do
  let path := categoryDir category / name
  IO.FS.readFile path

/-- Read a fixture file, returning none if it doesn't exist -/
def readFixtureOpt (category : String) (name : String) : IO (Option String) := do
  let path := categoryDir category / name
  try
    let content ← IO.FS.readFile path
    return some content
  catch _ =>
    return none

/-- Read the expected output for a fixture (from .expected file) -/
def readExpected (category : String) (name : String) : IO (Option String) := do
  readFixtureOpt category (name ++ ".expected")

/-- List all fixture files in a category -/
def listFixtures (category : String) : IO (Array System.FilePath) := do
  let dir := categoryDir category
  let entries ← dir.readDir
  let files := entries.filter (fun e => !e.fileName.endsWith ".expected")
  return files.map (·.path)

/-- A test case loaded from a fixture -/
structure TestCase where
  name : String
  source : String
  expected : Option String
  deriving Repr

/-- Load a single test case from a fixture -/
def loadTestCase (category : String) (name : String) : IO TestCase := do
  let source ← readFixture category name
  let expected ← readExpected category name
  return { name, source, expected }

/-- Load all test cases from a category -/
def loadAllTestCases (category : String) : IO (Array TestCase) := do
  let files ← listFixtures category
  let mut cases : Array TestCase := #[]
  for file in files do
    let name := file.fileName.getD "unknown"
    -- Skip .expected files
    if !name.endsWith ".expected" then
      let source ← IO.FS.readFile file
      let expected ← readExpected category name
      cases := cases.push { name, source, expected }
  return cases

/-- Result of running a test -/
inductive TestResult
  | passed : TestResult
  | failed (message : String) : TestResult
  | skipped (reason : String) : TestResult
  deriving Repr

/-- A simple test runner that tracks pass/fail counts -/
structure TestRunner where
  passed : Nat := 0
  failed : Nat := 0
  skipped : Nat := 0
  failures : Array String := #[]

namespace TestRunner

def init : TestRunner := {}

def recordPass (r : TestRunner) : TestRunner :=
  { r with passed := r.passed + 1 }

def recordFail (r : TestRunner) (msg : String) : TestRunner :=
  { r with failed := r.failed + 1, failures := r.failures.push msg }

def recordSkip (r : TestRunner) : TestRunner :=
  { r with skipped := r.skipped + 1 }

def record (r : TestRunner) (name : String) (result : TestResult) : TestRunner :=
  match result with
  | .passed => r.recordPass
  | .failed msg => r.recordFail s!"{name}: {msg}"
  | .skipped _ => r.recordSkip

def printSummary (r : TestRunner) (suiteName : String) : IO Unit := do
  IO.println s!"=== {suiteName} ==="
  IO.println s!"  Passed:  {r.passed}"
  IO.println s!"  Failed:  {r.failed}"
  IO.println s!"  Skipped: {r.skipped}"
  if !r.failures.isEmpty then
    IO.println "  Failures:"
    for f in r.failures do
      IO.println s!"    - {f}"

def isSuccess (r : TestRunner) : Bool := r.failed == 0

end TestRunner

end Test.Fixtures
