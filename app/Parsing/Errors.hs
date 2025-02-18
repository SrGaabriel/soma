module Parsing.Errors (ParsingError(..), getErrorToken) where
import Lexing.Lexer (Token (..), TokenKind, referenceToken, referenceTokenKind)
import Logging.ErrorPrinter (PrintableError(..))

data ParsingError
  = UnexpectedToken Token
  | ExpectedDifferentToken 
      { expected :: TokenKind
      , received :: Token 
      }
  | InvalidTokenForType Token
  | ExpectedIndentation Token -- for when a token isn't indented
  | ExpectedDifferentIndentation Token Int Int -- for when the indentation is wrong
  | UnseparatedStatements Token -- for when two statements are on the same line
  | InvalidIdentifierFollowup Token
  | EndOfInput
  | Debug 
  deriving (Eq)

instance Show ParsingError where
    show (UnexpectedToken t) = "Unexpected token " ++ referenceToken t
    show (ExpectedDifferentToken tExpected tReceived) = "Expected " ++ referenceTokenKind tExpected ++ " but received " ++ referenceToken tReceived
    show (InvalidTokenForType t) = "Invalid token for type: " ++ referenceToken t
    show (ExpectedIndentation _) = "Expected indentation"
    show (UnseparatedStatements t) = "Unseparated statements by newline at " ++ referenceToken t
    show (InvalidIdentifierFollowup t) = "Invalid identifier follow-up: " ++ referenceToken t
    show (ExpectedDifferentIndentation _ expc recv) = "Expected indentation of " ++ show expc ++ " spaces but received " ++ show recv
    show (EndOfInput) = "End of input"
    show Debug = "Debug"

instance PrintableError ParsingError where
    errorMessage err = show err

    errorStart (ExpectedIndentation t) = tokenPos t - 2 -- TODO: remove workaround
    errorStart (ExpectedDifferentIndentation t _ _) = tokenPos t + 1
    errorStart err = case getErrorToken err of
        Just t -> tokenPos t
        Nothing -> error "End of input has no position" 

    errorEnd (ExpectedIndentation t) = tokenPos t + length (tokenValue t) - 1
    errorEnd (ExpectedDifferentIndentation t _ _) = tokenPos t + length (tokenValue t) - 1
    errorEnd err = case getErrorToken err of
        Just t -> tokenPos t + length (tokenValue t) - 1
        Nothing -> error "End of input has no position"

getErrorToken :: ParsingError -> Maybe Token
getErrorToken (UnexpectedToken t) = Just t
getErrorToken (ExpectedDifferentToken _ t) = Just t
getErrorToken (InvalidTokenForType t) = Just t
getErrorToken (ExpectedIndentation t) = Just t
getErrorToken (InvalidIdentifierFollowup t) = Just t
getErrorToken (ExpectedDifferentIndentation t _ _) = Just t
getErrorToken (UnseparatedStatements t) = Just t
getErrorToken (EndOfInput) = Nothing -- TODO: replace with EOF token
getErrorToken Debug = Nothing