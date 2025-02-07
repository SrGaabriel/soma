module Parsing.Ops where

import Parsing.Tree (Expression(..))
import Lexing.Lexer (Token(..), TokenKind(..))

data Operator = Operator {
  opToken :: TokenKind,
  construct :: Token -> Expression -> Expression -> Expression
}

