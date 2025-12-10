import Soma
import Test.Fixtures

namespace Test.Parser

open Soma.Syntax
open Test.Fixtures

/-- Run a single parser test from a fixture -/
def runParserTest (tc : TestCase) (verbose : Bool := false) : IO TestResult := do
  -- Create a source file for parsing
  let sf := SourceFile.create ⟨0⟩ tc.name tc.source

  -- Lex first
  let (tokens, lexDiags) := lex tc.source
  if !lexDiags.isEmpty then
    IO.println s!"  [FAIL] {tc.name}: lexer errors"
    for d in lexDiags do
      IO.println s!"    - {d.message}"
    return .failed "lexer errors"

  -- Parse
  let (cst, parseDiags) := Parse.parseSourceFile.run' tokens sf

  -- Lower to AST
  let moduleName := tc.name.dropRight 5  -- Remove .soma extension
  let (astOpt, lowerDiags) := lower cst moduleName

  let allDiags := parseDiags ++ lowerDiags

  if allDiags.isEmpty then
    IO.println s!"  [PASS] {tc.name}"
    if verbose then
      match astOpt with
      | some ast => IO.println s!"    AST: {repr ast.decls}"
      | none => IO.println "    AST: (none)"
    return .passed
  else
    IO.println s!"  [FAIL] {tc.name}: {allDiags.size} errors"
    for d in allDiags do
      IO.println s!"    - {d.message}"
    return .failed s!"{allDiags.size} parse/lower errors"

/-- Run all parser tests from fixtures -/
def runFromFixtures (verbose : Bool := false) : IO TestRunner := do
  IO.println "=== Parser Tests (from fixtures) ==="
  let cases ← loadAllTestCases "parsing"
  let mut runner := TestRunner.init
  for tc in cases do
    let result ← runParserTest tc verbose
    runner := runner.record tc.name result
  return runner

/-- Main entry point for parser tests -/
def run : IO Unit := do
  let runner ← runFromFixtures
  runner.printSummary "Parser Summary"
  IO.println ""

end Test.Parser
