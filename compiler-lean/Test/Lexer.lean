import Soma
import Test.Fixtures

namespace Test.Lexer

open Soma.Syntax
open Test.Fixtures

/-- Run a single lexer test from a fixture -/
def runLexerTest (tc : TestCase) : IO TestResult := do
  let (tokens, diags) := lex tc.source
  -- For now, just check that lexing produces no errors
  if diags.isEmpty then
    IO.println s!"  [PASS] {tc.name}: {tokens.size} tokens"
    return .passed
  else
    IO.println s!"  [FAIL] {tc.name}: {diags.size} errors"
    for d in diags do
      IO.println s!"    - {d.message}"
    return .failed s!"{diags.size} lexer errors"

/-- Run all lexer tests from fixtures -/
def runFromFixtures : IO TestRunner := do
  IO.println "=== Lexer Tests (from fixtures) ==="
  let cases ← loadAllTestCases "lexing"
  let mut runner := TestRunner.init
  for tc in cases do
    let result ← runLexerTest tc
    runner := runner.record tc.name result
  return runner

/-- Run legacy inline tests (for comparison during migration) -/
def runInlineTests : IO Unit := do
  IO.println "=== Lexer Tests (inline) ==="

  -- Test 1: Simple identifier
  let (tokens, diags) := lex "hello"
  IO.println s!"Test 1 (identifier): {tokens.size} tokens, {diags.size} errors"
  for tok in tokens do
    IO.println s!"  {tok.kind} \"{tok.text}\""

  -- Test 2: Keywords
  let (tokens, diags) := lex "def let case if then else"
  IO.println s!"Test 2 (keywords): {tokens.size} tokens, {diags.size} errors"
  for tok in tokens do
    IO.println s!"  {tok.kind} \"{tok.text}\""

  -- Test 3: Numbers and operators
  let (tokens, diags) := lex "42 + 10 - 5"
  IO.println s!"Test 3 (numbers/ops): {tokens.size} tokens, {diags.size} errors"
  for tok in tokens do
    IO.println s!"  {tok.kind} \"{tok.text}\""

  IO.println "=== Inline Tests Complete ==="

/-- Main entry point for lexer tests -/
def run : IO Unit := do
  -- Run fixture-based tests
  let runner ← runFromFixtures
  runner.printSummary "Lexer Summary"
  IO.println ""

end Test.Lexer
