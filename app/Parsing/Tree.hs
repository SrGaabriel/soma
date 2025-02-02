
module Parsing.Tree where

import Lexing.Lexer (Token)

data Expression = Expression 
  { exprToken :: Token
  , exprKind :: ExpressionKind
  , exprChildren :: [Expression]
  } deriving (Show, Eq)

data ExpressionKind
  = RootExpr
  | FunctionExpr
  deriving (Show, Eq)