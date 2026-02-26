import Test.E2E.Config
import Test.E2E.Fixtures
import Test.Fixtures
import Soma.Driver.Options
import Somac.Build

namespace Test.E2E

open Test.Fixtures (TestResult TestRunner)
open Soma.Driver (BuildOptions)
open Somac.Build (build BuildResult)

/-- Result of running a process -/
structure ProcessResult where
  exitCode : UInt32
  stdout : String
  stderr : String
  deriving Repr

/-- Run a process and capture output -/
def runProcess (cmd : String) (args : Array String) : IO ProcessResult := do
  let config : IO.Process.SpawnArgs := {
    cmd := cmd
    args := args
    stdout := .piped
    stderr := .piped
  }
  let proc ← IO.Process.spawn config
  let stdout ← proc.stdout.readToEnd
  let stderr ← proc.stderr.readToEnd
  let exitCode ← proc.wait
  return { exitCode, stdout, stderr }

/-- Normalize line endings and trailing whitespace for comparison -/
def normalizeOutput (s : String) : String :=
  s.replace "\r\n" "\n" |>.trimAsciiEnd.toString

/-- Format diagnostics for error output -/
def formatDiagnostics (diags : Array Soma.Syntax.Diagnostic) : String :=
  let msgs := diags.map fun d => s!"{d.severity}: {d.message}"
  String.intercalate "\n" msgs.toList

/-- Run the test body, returning the result -/
private def runTestBody (tc : TestCase) (tempDir : System.FilePath) : IO (String × TestResult) := do
  let testId := s!"e2e/{tc.name}"

  setupTestDir tc tempDir

  let srcDir := tempDir / "src"
  let outputPath := if System.Platform.isWindows then
    tempDir / "output.exe"
  else
    tempDir / "output"

  let buildOpts : BuildOptions := {
    input := srcDir.toString
    output := some outputPath.toString
    emitLlvm := true
  }

  let buildResult ← build buildOpts

  if !buildResult.success then
    let diagMsg := formatDiagnostics buildResult.diagnostics
    return (testId, .failed s!"Compilation failed:\n{diagMsg}")

  unless ← outputPath.pathExists do
    return (testId, .failed s!"Compilation succeeded but output file not found: {outputPath}")

  let runResult ← runProcess outputPath.toString #[]

  if runResult.exitCode ≠ tc.expectedExitCode then
    return (testId, .failed s!"Exit code mismatch: expected {tc.expectedExitCode}, got {runResult.exitCode}\nstdout: {runResult.stdout}\nstderr: {runResult.stderr}")

  if let some expected := tc.expectedStdout then
    let actualNorm := normalizeOutput runResult.stdout
    let expectedNorm := normalizeOutput expected
    if actualNorm ≠ expectedNorm then
      return (testId, .failed s!"stdout mismatch:\n--- expected ---\n{expectedNorm}\n--- actual ---\n{actualNorm}")

  return (testId, .passed)

/-- Run a single E2E test case -/
def runTestCase (config : Config) (tc : TestCase) : IO (String × TestResult) := do
  let tempDir ← createTempDir tc.name

  let result ← runTestBody tc tempDir |>.catchExceptions fun e =>
    pure (s!"e2e/{tc.name}", .failed s!"Exception: {e}")

  -- Keep temp dir on failure for debugging
  let passed := match result with | (_, .passed) => true | _ => false
  unless config.keepTemp || !passed do
    removeDirRecursive tempDir |>.catchExceptions fun _ => pure ()

  return result

/-- Run all E2E tests -/
def runAll (config : Config) : IO TestRunner := do
  let cases ← discoverTestCases
  let mut runner := TestRunner.init

  if cases.isEmpty then
    IO.println "  No E2E test cases found"
    return runner

  for tc in cases do
    let (name, result) ← runTestCase config tc
    runner := runner.record name result
    match result with
    | .passed => IO.println s!"  ✓ {tc.name}"
    | .failed msg => do
      IO.println s!"  ✗ {tc.name}: {msg}"
      IO.println s!"    Artifacts preserved in: .lake/e2e-temp/{tc.name}-*"
    | .skipped reason => IO.println s!"  ○ {tc.name}: {reason}"

  return runner

end Test.E2E
