module Parsing.Ops where

import Parsing.Tree (BinaryOp(..))
import Lexing.Lexer (TokenKind(..))


data Operator = Operator
  { op :: BinaryOp
  , opToken :: TokenKind
  }

additive :: [Operator]
additive = 
  [ Operator BinaryAdd TokenPlus
  , Operator BinarySubtract TokenMinus ]

multiplicative :: [Operator]
multiplicative = 
  [ Operator BinaryMultiply TokenAsterisk
  , Operator BinaryDivide TokenSlash ]