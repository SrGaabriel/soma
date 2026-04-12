namespace Test.E2E

/-- Base directory for E2E fixtures -/
def fixturesDir : System.FilePath := "Test/fixtures/e2e"

/-- Shared primitive lang-items fixture used by tests -/
def sharedPrimPath : System.FilePath := "Test/fixtures/shared/prim.soma"

/-- Source type for a test case -/
inductive TestSource where
  | directory (path : System.FilePath)
  | singleFile (path : System.FilePath)
  deriving Repr

/-- An E2E test case loaded from a fixture directory or single file -/
structure TestCase where
  /-- Name of the test -/
  name : String
  /-- Source location -/
  source : TestSource
  /-- Expected stdout content -/
  expectedStdout : Option String
  /-- Expected exit code -/
  expectedExitCode : UInt32
  /-- Required library dependencies -/
  requiredDeps : Array String := #[]
  /-- Per-test execution timeout in milliseconds -/
  runTimeout : Option Nat := none
  deriving Repr

namespace TestCase

/-- Parse inline expected values from file comments -/
def parseInlineExpected (content : String) : Option String × UInt32 := Id.run do
  let lines := content.splitOn "\n"
  let mut stdout : Option String := none
  let mut exitCode : UInt32 := 0

  for line in lines do
    let trimmed := line.trimAscii.toString
    if !trimmed.startsWith "//" && !trimmed.isEmpty then
      break

    if trimmed.startsWith "// expected stdout:" then
      let value := (trimmed.drop 18).trimAscii.toString
      stdout := some value
    else if trimmed.startsWith "// expected exit:" then
      let value := (trimmed.drop 17).trimAscii.toString
      if let some n := value.toNat? then
        exitCode := n.toUInt32

  (stdout, exitCode)

/-- Parse a deps file listing required library dependencies one per line -/
def parseDepsFile (path : System.FilePath) : IO (Array String) := do
  if ← path.pathExists then
    let content ← IO.FS.readFile path
    let lines := content.splitOn "\n"
      |>.map (·.trimAscii.toString)
      |>.filter (!·.isEmpty)
    return lines.toArray
  else
    pure #[]

/-- Load a test case from a fixture directory -/
def loadFromDir (dir : System.FilePath) : IO TestCase := do
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

  -- Read dependency requirements
  let requiredDeps ← parseDepsFile (dir / "deps")

  let timeoutPath := dir / "expected.timeout"
  let runTimeout ← if ← timeoutPath.pathExists then
    let content ← IO.FS.readFile timeoutPath
    pure (content.trimAscii.toString.toNat?)
  else
    pure none

  return {
    name
    source := .directory dir
    expectedStdout
    expectedExitCode
    requiredDeps
    runTimeout
  }

/-- Load a test case from a single .soma file -/
def loadFromFile (file : System.FilePath) : IO TestCase := do
  let name := file.fileStem.getD "unknown"
  let content ← IO.FS.readFile file
  let (expectedStdout, expectedExitCode) := parseInlineExpected content

  return {
    name
    source := .singleFile file
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
          let tc ← TestCase.loadFromDir entry.path
          cases := cases.push tc
      else
        let ext := entry.path.extension.getD ""
        if ext == "soma" then
          let tc ← TestCase.loadFromFile entry.path
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
  let dstDir := tempDir / "src"
  match tc.source with
  | .directory dir =>
    let srcDir := dir / "src"
    copyDirRecursive srcDir dstDir
  | .singleFile file =>
    IO.FS.createDirAll dstDir
    let content ← IO.FS.readBinFile file
    IO.FS.writeBinFile (dstDir / file.fileName.getD "main.soma") content

  -- Only inject the shared prim.soma for standalone tests.
  -- Tests with library deps get their primitives from base.
  if tc.requiredDeps.isEmpty then
    let primSource ← IO.FS.readFile sharedPrimPath
    IO.FS.writeFile (dstDir / "prim.soma") primSource

end Test.E2E
