module Parsing.Errors (ParsingError(..), getErrorToken) where
import Lexing.Lexer (Token (..), TokenKind)
import Logging.ErrorPrinter (PrintableError(..))

data ParsingError
  = UnexpectedToken Token
  | ExpectedDifferentToken 
      { expected :: TokenKind
      , received :: Token 
      }
  | InvalidTokenForType Token
  | EndOfInput
  | Debug 
  deriving (Eq)

instance Show ParsingError where
  show (UnexpectedToken t) = "Unexpected token: " ++ show t
  show (ExpectedDifferentToken tExpected tReceived) = "Expected token '" ++ show tExpected ++ "' but received " ++ show (tokenValue tReceived)
  show (InvalidTokenForType t) = "Invalid token for type: " ++ show t
  show (EndOfInput) = "End of input"
  show Debug = "Debug"

instance PrintableError ParsingError where
  errorMessage err = show err
  errorStart err = case getErrorToken err of
    Just t -> tokenPos t
    Nothing -> error "End of input has no position" 
  errorEnd err = case getErrorToken err of
    Just t -> tokenPos t + length (tokenValue t) - 1
    Nothing -> error "End of input has no position"

getErrorToken :: ParsingError -> Maybe Token
getErrorToken (UnexpectedToken t) = Just t
getErrorToken (ExpectedDifferentToken _ t) = Just t
getErrorToken (InvalidTokenForType t) = Just t
getErrorToken (EndOfInput) = Nothing -- TODO: replace with EOF token
getErrorToken Debug = Nothing