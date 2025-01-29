module Parsing.Errors (ParsingError(..)) where

data ParsingError = 
    UnexpectedToken String
    deriving (Show, Eq)