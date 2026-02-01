namespace Test.E2E

/-- Base directory for E2E fixtures -/
def fixturesDir : System.FilePath := "Test/fixtures/e2e"

/-- An E2E test case loaded from a fixture directory -/
structure TestCase where
  /-- Name of the test (directory name) -/
  name : String
  /-- Path to the fixture directory -/
  fixtureDir : System.FilePath
  /-- Expected stdout content -/
  expectedStdout : Option String
  /-- Expected exit code -/
  expectedExitCode : UInt32
  deriving Repr

namespace TestCase

/-- Load a test case from a fixture directory -/
def load (dir : System.FilePath) : IO TestCase := do
  let name := dir.fileName.getD "unknown"

  -- Read expected stdout
  let stdoutPath := dir / "expected.stdout"
  let expectedStdout ← if ← stdoutPath.pathExists then
    some <$> IO.FS.readFile stdoutPath
  else
    pure none

  -- Read expected exit code
  let exitPath := dir / "expected.exit"
  let expectedExitCode ← if ← exitPath.pathExists then
    let content ← IO.FS.readFile exitPath
    match content.trimAscii.toString.toNat? with
    | some n => pure n.toUInt32
    | none => pure 0
  else
    pure 0

  return {
    name
    fixtureDir := dir
    expectedStdout
    expectedExitCode
  }

end TestCase

/-- Discover all E2E test cases in the fixtures directory -/
def discoverTestCases : IO (Array TestCase) := do
  let mut cases : Array TestCase := #[]

  if ← fixturesDir.pathExists then
    let entries ← fixturesDir.readDir
    for entry in entries do
      if ← entry.path.isDir then
        let srcDir := entry.path / "src"
        if ← srcDir.pathExists then
          let tc ← TestCase.load entry.path
          cases := cases.push tc

  return cases.qsort (·.name < ·.name)

/-- Copy a directory recursively -/
partial def copyDirRecursive (src dst : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dst
  let entries ← src.readDir
  for entry in entries do
    let srcPath := entry.path
    let dstPath := dst / entry.fileName
    if ← srcPath.isDir then
      copyDirRecursive srcPath dstPath
    else
      let content ← IO.FS.readBinFile srcPath
      IO.FS.writeBinFile dstPath content

/-- Remove a directory recursively -/
partial def removeDirRecursive (path : System.FilePath) : IO Unit := do
  if ← path.pathExists then
    if ← path.isDir then
      let entries ← path.readDir
      for entry in entries do
        removeDirRecursive entry.path
      IO.FS.removeDir path
    else
      IO.FS.removeFile path

/-- Create a temporary directory for a test -/
def createTempDir (testName : String) : IO System.FilePath := do
  let timestamp ← IO.monoMsNow
  let tempBase : System.FilePath := ".lake/e2e-temp"
  let tempDir := tempBase / s!"{testName}-{timestamp}"
  IO.FS.createDirAll tempDir
  return tempDir

/-- Set up a test case in a temporary directory -/
def setupTestDir (tc : TestCase) (tempDir : System.FilePath) : IO Unit := do
  let srcDir := tc.fixtureDir / "src"
  let dstDir := tempDir / "src"
  copyDirRecursive srcDir dstDir

end Test.E2E
