module Syntax.Ops (BinaryOp(..)) where

data BinaryOp = BinaryAdd | BinarySubtract | BinaryMultiply | BinaryDivide
    deriving (Show, Eq, Ord)