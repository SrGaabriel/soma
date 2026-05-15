
import Soma.Project.Check
import Soma.Diagnostic
import Psychopomp.Driver.Flush
import Test.Fixtures
import Test.Dependent.Integration

namespace Test.Diagnostic.Snapshot

open Soma.Project.Check
open Test.Fixtures

def renderCfg : Psychopomp.RenderConfig :=
  { colorMode := .never, glyphSet := .ascii, tabWidth := 4 }

def fixturesDir : System.FilePath := "Test/fixtures/diagnostics"

def normalisePaths (s : String) : String :=
  s.replace "\\" "/"

def renderAll (repo : Soma.SubstrateRepo) (ds : Array Psychopomp.Diagnostic) : String :=
  let collapsed := Soma.Diagnostic.Cascade.collapse ds
  let parts := collapsed.map Soma.Render.assignIdRec |>.toList.filterMap fun d =>
    match Psychopomp.Driver.Flush.render d renderCfg repo with
    | .ok s => some (normalisePaths s)
    | .error _ => none
  String.intercalate "\n\n" parts

def recordMode : IO Bool := do
  match ← IO.getEnv "SOMA_RECORD_SNAPSHOTS" with
  | none => return false
  | some s =>
    let t := s.trimAscii
    return !(t.isEmpty || t == "0" || t == "false")

def firstDiffLine (a b : String) : Option Nat := Id.run do
  let la := a.splitOn "\n"
  let lb := b.splitOn "\n"
  let mut i : Nat := 0
  let mut la' := la
  let mut lb' := lb
  while !la'.isEmpty || !lb'.isEmpty do
    match la', lb' with
    | x :: xs, y :: ys =>
      if x != y then return some i
      la' := xs
      lb' := ys
    | [], _ :: _ => return some i
    | _ :: _, [] => return some i
    | [], [] => return none
    i := i + 1
  return none

def quoteLines (prefix_ : String) (s : String) : String :=
  (s.splitOn "\n").map (prefix_ ++ ·) |> String.intercalate "\n"

def readSnap (fixturePath : System.FilePath) : IO (Option String) := do
  let snapPath := fixturePath.withExtension "snap"
  try
    return some (← IO.FS.readFile snapPath)
  catch _ => return none

def writeSnap (fixturePath : System.FilePath) (content : String) : IO Unit := do
  let snapPath := fixturePath.withExtension "snap"
  IO.FS.writeFile snapPath content

def renderFixture (fixturePath : System.FilePath) : IO String := do
  let name := (fixturePath.fileStem.getD "fixture")
  let config : ProjectConfig := {
    input := fixturePath
    name := some name
    deps := #[]
  }
  let result ← checkSingleFile config Test.Dependent.Integration.noDepsLoader
  pure (renderAll result.diagCtx.repo result.diagnostics)

def runFixture (fixturePath : System.FilePath) : IO TestResult := do
  let actual ← renderFixture fixturePath
  let record ← recordMode
  match ← readSnap fixturePath with
  | none =>
    if record then
      writeSnap fixturePath actual
      return .passed
    else
      return .failed s!"missing .snap (run with SOMA_RECORD_SNAPSHOTS=1 to record)\nrendered:\n{quoteLines "  | " actual}"
  | some expected =>
    if expected == actual then
      return .passed
    else if record then
      writeSnap fixturePath actual
      return .passed
    else
      let lineNo := firstDiffLine expected actual |>.getD 0
      let msg :=
        s!"snapshot mismatch (first differing line: {lineNo})\n" ++
        s!"  expected:\n{quoteLines "  | " expected}\n" ++
        s!"  actual:\n{quoteLines "  | " actual}\n" ++
        s!"  (run with SOMA_RECORD_SNAPSHOTS=1 to update)"
      return .failed msg

def listFixtures : IO (Array System.FilePath) := do
  let dir := fixturesDir
  try
    let entries ← dir.readDir
    let somaFiles := entries.filter fun e =>
      e.path.extension == some "soma"
    return somaFiles.map (·.path)
  catch _ => return #[]

def runFromFixtures : IO TestRunner := do
  IO.println "=== Diagnostic Snapshots ==="
  let mut runner := TestRunner.init
  let fixtures ← listFixtures
  if fixtures.isEmpty then
    IO.println "  (no .soma fixtures present, snapshot runner is wired but empty)"
    return runner
  for path in fixtures do
    let name := path.fileStem.getD path.toString
    let result ← runFixture path
    match result with
    | .passed => IO.println s!"  [PASS] {name}"
    | .failed msg => IO.println s!"  [FAIL] {name}: {msg}"
    | .skipped reason => IO.println s!"  [SKIP] {name}: {reason}"
    runner := runner.record name result
  return runner

def run : IO TestRunner := do
  let r ← runFromFixtures
  IO.println ""
  r.printSummary "Diagnostic Snapshots"
  IO.println ""
  return r

end Test.Diagnostic.Snapshot
