import Soma
import Test.Fixtures

namespace Test.GreenTree

open Soma.Syntax
open Test.Fixtures

/-- Get all fixture categories -/
def allCategories : Array String := #["parsing", "lexing", "checking", "dependent"]

/-- Load all .soma files from a directory recursively -/
def loadAllSomaFiles (dir : System.FilePath) : IO (Array (System.FilePath × String)) := do
  let mut results : Array (System.FilePath × String) := #[]
  let entries ← dir.readDir
  for entry in entries do
    if entry.fileName.endsWith ".soma" then
      let content ← IO.FS.readFile entry.path
      results := results.push (entry.path, content)
  return results

/-- Run the green tree size test for a single file -/
def runGreenTreeSizeTest (path : System.FilePath) (source : String) : IO TestResult := do
  let name := path.fileName.getD "unknown"
  let sf := SourceFile.create ⟨0⟩ name source
  let (tree, _) := parseToTree sf
  let greenWidth := tree.green.width
  let sourceByteSize := source.utf8ByteSize
  if greenWidth == sourceByteSize then
    IO.println s!"  [PASS] {name}: green width = source bytes = {greenWidth}"
    return .passed
  else
    IO.println s!"  [FAIL] {name}: green width ({greenWidth}) != source bytes ({sourceByteSize})"
    return .failed s!"green width ({greenWidth}) != source bytes ({sourceByteSize})"

/-- Run green tree size tests for all fixtures -/
def runFromFixtures : IO TestRunner := do
  IO.println "=== Green Tree Size Tests ==="
  let mut runner := TestRunner.init
  for category in allCategories do
    let dir := fixturesDir / category
    -- Check if directory exists
    if ← dir.pathExists then
      let files ← loadAllSomaFiles dir
      for (path, content) in files do
        let result ← runGreenTreeSizeTest path content
        let name := path.fileName.getD "unknown"
        runner := runner.record s!"{category}/{name}" result
  return runner

/-- Main entry point for green tree tests -/
def run : IO TestRunner := do
  let runner ← runFromFixtures
  runner.printSummary "Green Tree Summary"
  IO.println ""
  return runner

end Test.GreenTree
