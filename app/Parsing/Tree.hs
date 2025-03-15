module Parsing.Tree (Expression(..), ExpressionKind(..), exprChildren) where

import Lexing.Lexer (Token(..))
import Parsing.Type (Type)
import Parsing.Ops (BinaryOp)
import qualified Data.Map as Map

data Expression = Expression 
  { exprToken :: Token
  , exprKind :: ExpressionKind
  } deriving (Eq, Ord)

data ExpressionKind
  = RootExpr
    { rootLeaves :: [Expression] }
  | FunctionExpr
    { functionName :: String
    , functionParams :: Map.Map String Type
    , functionReturnType   :: Type
    , functionBody :: Expression }
  | FunctionParamExpr
    { fnParamName :: Maybe String
    , fnParamType :: Type }
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
  | StringExpr String
  | BlockExpr
    { blockExpressions :: [Expression] }
  | FunctionCallExpr
    { functionCallName :: String
    , functionCallArgs :: [Expression] }
  | VariableReferenceExpr
    { variableReferenceName :: String }
  deriving (Eq, Ord)

exprChildren :: ExpressionKind -> [Expression]
exprChildren kind = case kind of
    RootExpr leaves -> leaves
    FunctionExpr _ _ _ body -> [body]
    FunctionParamExpr _ _ -> []
    BinaryOpExpr left right _ -> [left, right]
    PatternMatchExpr patterns -> patterns
    NumberPatternExpr _ -> []
    VariablePatternExpr _ -> []
    PatternHandlerExpr pattern -> [pattern]
    NumberExpr -> []
    FunctionCallExpr _ args -> args
    VariableReferenceExpr _ -> []
    StringExpr _ -> []
    BlockExpr expressions -> expressions

instance Show ExpressionKind where
    show kind = case kind of
        RootExpr _ -> "RootExpr"
        FunctionExpr name params returnType _ -> "FunctionExpr (" ++ name ++ " :: " ++ show params ++ " -> " ++ show returnType ++ ")"
        FunctionParamExpr name paramType -> "FunctionParamExpr (" ++ show name ++ " :: " ++ show paramType ++ ")"
        BinaryOpExpr left right operator -> "BinaryOpExpr (" ++ show left ++ " " ++ show operator ++ " " ++ show right ++ ")"
        PatternMatchExpr _ -> "PatternMatchExpr"
        NumberPatternExpr value -> "NumberPatternExpr (" ++ value ++ ")"
        VariablePatternExpr name -> "VariablePatternExpr (" ++ name ++ ")"
        PatternHandlerExpr pattern -> "PatternHandlerExpr (" ++ show pattern ++ ")"
        NumberExpr -> "NumberExpr"
        FunctionCallExpr name _ -> "FunctionCallExpr (" ++ name ++ ")"
        VariableReferenceExpr name -> "VariableReferenceExpr (" ++ name ++ ")"
        BlockExpr _ -> "BlockExpr"
        StringExpr value -> "StringExpr (" ++ value ++ ")"

instance Show Expression where
  show (Expression token kind) = (show kind) ++ " '" ++ tokenValue token ++ "'"