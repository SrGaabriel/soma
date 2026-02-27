import Test.Fixtures
import Test.Lexer
import Test.Parser
import Test.GreenTree
import Test.Error
import Test.Dependent.Core
import Test.Dependent.Infer
import Test.Dependent.Unify
import Test.Dependent.Graph
import Test.Dependent.Usage
import Test.Dependent.Level
import Test.Dependent.Instance
import Test.Dependent.Equality
import Test.Dependent.Totality
import Test.Dependent.Integration
import Test.Alloy
import Test.Circuit
import Test.Circuit.Reduce
import Test.PatternMatch
import Test.E2E

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

  -- Run green tree size tests
  let greenTreeRunner ← Test.GreenTree.run
  total := total.merge greenTreeRunner

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

  -- Run constraint graph tests (Phase 3b)
  let graphRunner ← Test.Dependent.Graph.run
  total := total.merge graphRunner

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

  -- Run Alloy IR tests
  let alloyRunner ← Test.Alloy.run
  total := total.merge alloyRunner

  -- Run Circuit IR tests
  let circuitRunner ← Test.Circuit.run
  total := total.merge circuitRunner

  -- Run Circuit Reducer tests
  let reduceRunner ← Test.Circuit.Reduce.run
  total := total.merge reduceRunner

  -- Run Pattern Match Compilation tests
  let patternMatchRunner ← Test.PatternMatch.run
  total := total.merge patternMatchRunner

  -- Run E2E tests (requires somac binary and runtime)
  let e2eRunner ← Test.E2E.run
  total := total.merge e2eRunner

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
