import Test.Fixtures
import Test.Lexer
import Test.Parser
import Test.Error
import Test.Dependent.Core
import Test.Dependent.Infer
import Test.Dependent.Unify
import Test.Dependent.Usage
import Test.Dependent.Level
import Test.Dependent.Instance
import Test.Dependent.Equality
import Test.Dependent.Totality
import Test.Dependent.Integration

open Test.Fixtures

/-- Main entry point for all tests -/
def main : IO UInt32 := do
  IO.println "Running Soma Compiler Tests"
  IO.println "============================"
  IO.println ""

  let mut total := TestRunner.init

  -- Run lexer tests
  let lexerRunner ← Test.Lexer.run
  total := total.merge lexerRunner

  -- Run parser tests
  let parserRunner ← Test.Parser.run
  total := total.merge parserRunner

  -- Run error rendering tests (visual only)
  let errorRunner ← Test.Error.run
  total := total.merge errorRunner

  -- Run dependent types core tests (Phase 1)
  let coreRunner ← Test.Dependent.Core.run
  total := total.merge coreRunner

  -- Run dependent types infer tests (Phase 2)
  let inferRunner ← Test.Dependent.Infer.run
  total := total.merge inferRunner

  -- Run dependent types unify tests (Phase 3)
  let unifyRunner ← Test.Dependent.Unify.runAllTests
  total := total.merge unifyRunner

  -- Run dependent types usage tests (Phase 4)
  let usageRunner ← Test.Dependent.Usage.run
  total := total.merge usageRunner

  -- Run dependent types level tests (Phase 5)
  let levelRunner ← Test.Dependent.Level.run
  total := total.merge levelRunner

  -- Run dependent types instance tests (Phase 6)
  let instanceRunner ← Test.Dependent.Instance.run
  total := total.merge instanceRunner

  -- Run dependent types equality tests (Phase 8)
  let equalityRunner ← Test.Dependent.Equality.runAllTests
  total := total.merge equalityRunner

  -- Run dependent types totality tests (Phase 9)
  let totalityRunner ← Test.Dependent.Totality.runAllTests
  total := total.merge totalityRunner

  -- Run dependent types integration tests (Phase 10)
  let integrationRunner ← Test.Dependent.Integration.run
  total := total.merge integrationRunner

  IO.println ""
  IO.println "════════════════════════════════════════════════════════════════"
  IO.println "                        FINAL SUMMARY"
  IO.println "════════════════════════════════════════════════════════════════"
  IO.println s!"  Total Passed:  {total.passed}"
  IO.println s!"  Total Failed:  {total.failed}"
  IO.println s!"  Total Skipped: {total.skipped}"

  if total.failed > 0 then
    IO.println ""
    IO.println "FAILURES:"
    for f in total.failures do
      IO.println s!"  - {f}"
    IO.println ""
    return 1
  else
    IO.println ""
    IO.println "All tests passed!"
    return 0
