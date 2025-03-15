module Parsing.Ops where

data BinaryOp = BinaryAdd | BinarySubtract | BinaryMultiply | BinaryDivide
    deriving (Show, Eq, Ord)