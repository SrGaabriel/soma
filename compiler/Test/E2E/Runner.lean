import Test.E2E.Config
import Test.E2E.Fixtures
import Test.Fixtures
import Soma.Driver.Options
import Somac.Build

namespace Test.E2E

open Test.Fixtures (TestResult TestRunner)
open Soma.Driver (BuildOptions OptProfile)
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

/-- Root paths for base and stdlib source directories, relative to compiler/ -/
def baseSourceDir : System.FilePath := ".." / "base" / "src"
def stdlibSourceDir : System.FilePath := ".." / "stdlib" / "src"

/-- Cache directory for pre-built .toria library artifacts -/
def libCacheDir : System.FilePath := ".lake" / "e2e-temp" / "libs"

/-- Known library dependency graph: base has no deps, stdlib depends on base -/
def libraryDeps : String → Array String
  | "stdlib" => #["base"]
  | _ => #[]

/-- Source directory for a known library -/
def librarySourceDir : String → Option System.FilePath
  | "base" => some baseSourceDir
  | "stdlib" => some stdlibSourceDir
  | _ => none

/-- Cached .toria artifacts built lazily on first use -/
structure LibCache where
  artifacts : Std.HashMap String System.FilePath := {}

/-- Build a library to a .toria artifact resolving transitive deps first -/
partial def LibCache.ensure (cache : LibCache) (lib : String) : IO (LibCache × System.FilePath) := do
  -- Return cached artifact if already built
  if let some path := cache.artifacts.get? lib then
    return (cache, path)

  let srcDir ← match librarySourceDir lib with
    | some d => pure d
    | none => throw (.userError s!"Unknown library dependency: {lib}")

  unless ← srcDir.pathExists do
    throw (.userError s!"Library source not found: {srcDir}")

  -- Recursively build transitive dependencies first
  let deps := libraryDeps lib
  let mut cache := cache
  let mut depPairs : Array (String × String) := #[]
  for dep in deps do
    let (cache', depPath) ← cache.ensure dep
    cache := cache'
    depPairs := depPairs.push (dep, depPath.toString)

  -- Build the library
  IO.FS.createDirAll libCacheDir
  let outputPath := libCacheDir / s!"{lib}.toria"

  -- Skip rebuild if artifact already exists on disk
  if ← outputPath.pathExists then
    let cache' := { cache with artifacts := cache.artifacts.insert lib outputPath }
    return (cache', outputPath)

  let buildOpts : BuildOptions := {
    input := srcDir.toString
    output := some outputPath.toString
    name := some lib
    lib := true
    deps := depPairs
  }

  let result ← build buildOpts
  unless result.success do
    let diagMsg := formatDiagnostics result.diagnostics
    throw (.userError s!"Failed to build library '{lib}':\n{diagMsg}")

  let cache' := { cache with artifacts := cache.artifacts.insert lib outputPath }
  return (cache', outputPath)

/-- Resolve all dependencies for a test case, building libraries as needed -/
def LibCache.resolveTestDeps (cache : LibCache) (tc : TestCase)
    : IO (LibCache × Array (String × String)) := do
  if tc.requiredDeps.isEmpty then
    return (cache, #[])

  let mut cache := cache
  let mut allDeps : Array (String × String) := #[]
  let mut resolved : Std.HashSet String := {}

  let mut queue := tc.requiredDeps.toList
  while !queue.isEmpty do
    match queue with
    | [] => break
    | dep :: rest =>
      queue := rest
      if resolved.contains dep then continue
      -- Add transitive deps to front of queue
      let transitive := libraryDeps dep
      queue := transitive.toList ++ queue
      resolved := resolved.insert dep

  for dep in tc.requiredDeps do
    let transitive := libraryDeps dep
    for tdep in transitive do
      if !allDeps.any (·.1 == tdep) then
        let (cache', path) ← cache.ensure tdep
        cache := cache'
        allDeps := allDeps.push (tdep, path.toString)
    if !allDeps.any (·.1 == dep) then
      let (cache', path) ← cache.ensure dep
      cache := cache'
      allDeps := allDeps.push (dep, path.toString)

  return (cache, allDeps)

/-- Run the test body, returning the result -/
private def runTestBody (tc : TestCase) (tempDir : System.FilePath)
    (deps : Array (String × String)) (profile : OptProfile) : IO (String × TestResult) := do
  let testId := s!"e2e/{tc.name}[{profile}]"

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
    deps := deps
    profile := profile
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

/-- All profiles to test against -/
private def allProfiles : Array OptProfile := #[.debug, .dev, .release]

/-- Run a single E2E test case against a specific profile -/
def runTestCase (config : Config) (cache : LibCache) (tc : TestCase) (profile : OptProfile)
    : IO (LibCache × String × TestResult) := do
  let tempDir ← createTempDir s!"{tc.name}-{profile}"

  let (cache, deps) ← cache.resolveTestDeps tc |>.catchExceptions fun e =>
    pure (cache, #[("_err", s!"{e}")])

  if deps.any (·.1 == "_err") then
    let errMsg := deps.find? (·.1 == "_err") |>.map (·.2) |>.getD "unknown"
    return (cache, s!"e2e/{tc.name}[{profile}]", .failed s!"Dependency resolution failed: {errMsg}")

  let result ← runTestBody tc tempDir deps profile |>.catchExceptions fun e =>
    pure (s!"e2e/{tc.name}[{profile}]", .failed s!"Exception: {e}")

  -- Keep temp dir on failure for debugging
  let passed := match result with | (_, .passed) => true | _ => false
  unless config.keepTemp || !passed do
    removeDirRecursive tempDir |>.catchExceptions fun _ => pure ()

  return (cache, result.1, result.2)

/-- Run all E2E tests against all optimization profiles -/
def runAll (config : Config) : IO TestRunner := do
  let cases ← discoverTestCases
  let mut runner := TestRunner.init
  let mut cache : LibCache := {}

  if cases.isEmpty then
    IO.println "  No E2E test cases found"
    return runner

  for tc in cases do
    for profile in allProfiles do
      let (cache', name, result) ← runTestCase config cache tc profile
      cache := cache'
      runner := runner.record name result
      match result with
      | .passed => IO.println s!"  ✓ {tc.name} [{profile}]"
      | .failed msg => do
        IO.println s!"  ✗ {tc.name} [{profile}]: {msg}"
        IO.println s!"    Artifacts preserved in: .lake/e2e-temp/{tc.name}-{profile}-*"
      | .skipped reason => IO.println s!"  ○ {tc.name} [{profile}]: {reason}"

  return runner

end Test.E2E
