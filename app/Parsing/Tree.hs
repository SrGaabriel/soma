
module Parsing.Tree where

import Lexing.Lexer (Token)
import Parsing.Type (Type)

data Expression = Expression 
  { exprToken :: Token
  , exprKind :: ExpressionKind
  , exprChildren :: [Expression]
  } deriving (Show, Eq)

data ExpressionKind
  = RootExpr
  | FunctionExpr
    { functionName :: String,
      returnType :: Type
    }
  deriving (Show, Eq)