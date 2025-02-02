module Parsing.Errors (ParsingError(..)) where
import Lexing.Lexer (Token)

data ParsingError
    = UnexpectedToken Token
    | EndOfInput
    deriving (Show, Eq)