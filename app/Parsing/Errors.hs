module Parsing.Errors (ParsingError(..)) where

data ParsingError 
    = UnexpectedToken String
    | EndOfInput
    deriving (Show, Eq)