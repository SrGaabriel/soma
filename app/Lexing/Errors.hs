module Lexing.Errors (LexingError(..)) where
import Logging.ErrorPrinter (PrintableError(..))

data LexingError
  = UnexpectedCharacter Char Int

instance PrintableError LexingError where
    errorMessage (UnexpectedCharacter c _) = "Unexpected character '" ++ [c] ++ "'"
    errorStart (UnexpectedCharacter _ i) = i
    errorEnd (UnexpectedCharacter _ i) = i + 1