module Parsing.Errors (ParsingError(..), getErrorToken, getErrorMessage) where
import Lexing.Lexer (Token (..), TokenKind)

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

getErrorMessage :: ParsingError -> String
getErrorMessage (UnexpectedToken t) = "Unexpected token: " ++ show t
getErrorMessage (ExpectedDifferentToken tExpected tReceived) = "Expected token '" ++ show tExpected ++ "' but received " ++ show (tokenValue tReceived)
getErrorMessage (InvalidTokenForType t) = "Invalid token for type: " ++ show t
getErrorMessage (EndOfInput) = "End of input"
getErrorMessage Debug = "Debug"

getErrorToken :: ParsingError -> Maybe Token
getErrorToken (UnexpectedToken t) = Just t
getErrorToken (ExpectedDifferentToken _ t) = Just t
getErrorToken (InvalidTokenForType t) = Just t
getErrorToken (EndOfInput) = Nothing
getErrorToken Debug = Nothing