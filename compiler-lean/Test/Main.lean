import Test.Fixtures
import Test.Lexer
import Test.Parser
import Test.Error
import Test.Infer

/-- Main entry point for all tests -/
def main : IO UInt32 := do
  IO.println "Running Soma Compiler Tests"
  IO.println "============================"
  IO.println ""

  -- Run lexer tests
  Test.Lexer.run

  -- Run parser tests
  Test.Parser.run

  -- Run type inference tests
  Test.Infer.run

  IO.println ""
  IO.println "All test suites completed."
  return 0
