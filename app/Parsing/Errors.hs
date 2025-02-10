module Parsing.Errors (ParsingError(..)) where
import Lexing.Lexer (Token, TokenKind)

data ParsingError
  = UnexpectedToken Token
  | ExpectedDifferentToken 
      { expected :: TokenKind
      , received :: Token 
      }
  | InvalidTokenForType Token
  | EndOfInput
  | Debug 
  deriving (Show, Eq)

getToken :: ParsingError -> Maybe Token
getToken (UnexpectedToken t) = Just t
getToken (ExpectedDifferentToken _ t) = Just t
getToken (InvalidTokenForType t) = Just t
getToken (EndOfInput) = Nothing
getToken Debug = Nothing