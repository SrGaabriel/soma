module Parsing.Tree where

import Lexing.Lexer (Token(..))
import Parsing.Type (Type)
import Parsing.Ops (BinaryOp)

data Expression = Expression 
  { exprToken :: Token
  , exprKind :: ExpressionKind
  } deriving (Eq)

data ExpressionKind
  = RootExpr
    { rootLeaves :: [Expression] }
  | FunctionExpr
    { functionName :: String
    , functionReturnType   :: Type
    , functionBody :: Expression }
  | BinaryOpExpr
    { binaryOpLeft :: Expression
    , binaryOpRight :: Expression
    , binaryOp :: BinaryOp }
  | PatternMatchExpr
    { patternMatchHandlers :: [Expression] }
  | NumberPatternExpr 
    { numberPatternValue :: String }
  | VariablePatternExpr
    { variablePatternName :: String }
  | PatternHandlerExpr
    { patternHandlerPattern :: Expression }
  | NumberExpr
  deriving (Eq)

getChildren :: ExpressionKind -> [Expression]
getChildren kind = case kind of
  RootExpr leaves -> leaves
  FunctionExpr _ _ body -> [body]
  BinaryOpExpr left right _ -> [left, right]
  PatternMatchExpr patterns -> patterns
  NumberPatternExpr _ -> []
  VariablePatternExpr _ -> []
  PatternHandlerExpr pattern -> [pattern]
  NumberExpr -> []

instance Show ExpressionKind where
  show kind = case kind of
    RootExpr _ -> "RootExpr"
    FunctionExpr name returnType _ -> "FunctionExpr (" ++ name ++ " -> " ++ show returnType ++ ")"
    BinaryOpExpr left right operator -> "BinaryOpExpr (" ++ show left ++ " " ++ show operator ++ " " ++ show right ++ ")"
    PatternMatchExpr _ -> "PatternMatchExpr"
    NumberPatternExpr value -> "NumberPatternExpr (" ++ value ++ ")"
    VariablePatternExpr name -> "VariablePatternExpr (" ++ name ++ ")"
    PatternHandlerExpr pattern -> "PatternHandlerExpr (" ++ show pattern ++ ")"
    NumberExpr -> "NumberExpr"

instance Show Expression where
  show (Expression token kind) = (show kind) ++ " '" ++ tokenValue token ++ "'"