module Parsing.Ops where

data BinaryOp = BinaryAdd | BinarySubtract | BinaryMultiply | BinaryDivide
  deriving (Show, Eq)

instance Ord BinaryOp where
  compare BinaryAdd BinaryAdd = EQ
  compare BinaryAdd _ = LT
  compare _ BinaryAdd = GT
  compare BinarySubtract BinarySubtract = EQ
  compare BinarySubtract _ = LT
  compare _ BinarySubtract = GT
  compare BinaryMultiply BinaryMultiply = EQ
  compare BinaryMultiply _ = LT
  compare _ BinaryMultiply = GT
  compare BinaryDivide BinaryDivide = EQ