
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
    { functionName :: String
    , returnType   :: Type
    , handler      :: FunctionHandler }
  | PatternMatch
  | NumberPatternExpr 
    { value :: String }
  | VariablePatternExpr
    { variableName :: String }
  | PatternHandlerExpr
  | NumberExpr
  deriving (Show, Eq)

data FunctionHandler = ExpressionHandler | PatternHandler
  deriving (Show, Eq)
