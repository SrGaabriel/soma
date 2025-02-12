module Lexing.Errors (LexingError(..)) where
import Logging.ErrorPrinter (PrintableError(..))

data LexingError
  = UnexpectedCharacter Char Int

instance PrintableError LexingError where
    errorMessage (UnexpectedCharacter c i) = "Unexpected character '" ++ [c] ++ "' at position " ++ show i
    errorStart (UnexpectedCharacter _ i) = i
    errorEnd (UnexpectedCharacter _ i) = i