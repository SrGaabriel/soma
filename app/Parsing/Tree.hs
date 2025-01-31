
module Parsing.Tree where

import Lexing.Lexer (Token)

data Expression = Expression 
  { token :: Token
  , kind :: ExpressionKind
  , children :: [Expression]
  } deriving (Show, Eq)

data ExpressionKind
  = RootExpr
  deriving (Show, Eq)