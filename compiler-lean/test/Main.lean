import Soma.Lexer.Tests

def main : IO UInt32 := do
  Soma.Lexer.Tests.testLexer
  return 0
