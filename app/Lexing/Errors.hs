module Lexing.Errors (LexingError (..)) where

import Logging.ErrorPrinter (PrintableError (..))

data LexingError
    = UnexpectedCharacter Char Int
    | UnterminatedString Int
    | UnterminatedIdentifier Int
    | UnterminatedComment Int

instance PrintableError LexingError where
    errorMessage (UnexpectedCharacter c _) = "Unexpected character '" ++ [c] ++ "'"
    errorMessage (UnterminatedString _) = "Unterminated string"
    errorMessage (UnterminatedIdentifier _) = "Unterminated identifier"
    errorMessage (UnterminatedComment _) = "Unterminated comment"
    errorStart (UnexpectedCharacter _ i) = i
    errorStart (UnterminatedString i) = i
    errorStart (UnterminatedIdentifier i) = i
    errorStart (UnterminatedComment i) = i
    errorEnd (UnexpectedCharacter _ i) = i + 1
    errorEnd (UnterminatedString i) = i + 1
    errorEnd (UnterminatedComment i) = i + 1
    errorEnd (UnterminatedIdentifier i) = i + 1
