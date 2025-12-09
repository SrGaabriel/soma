import Test.Lexer
import Test.Error

def main : IO UInt32 := do
  Test.Lexer.run
  Test.Error.run
  return 0
