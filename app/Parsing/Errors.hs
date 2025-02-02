module Parsing.Errors (ParsingError(..)) where
import Lexing.Lexer (Token, TokenKind)

data ParsingError
    = UnexpectedToken Token
  | ExpectedDifferentToken 
      { expected :: TokenKind
      , received :: Token 
      } 
    | EndOfInput
    deriving (Show, Eq)