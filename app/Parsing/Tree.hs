{-# LANGUAGE InstanceSigs #-}

module Parsing.Tree (Expression (..), ExpressionKind (..), exprChildren) where

import Lexing.Lexer (Token (..))
import Parsing.Ops (BinaryOp)
import Parsing.Type (Type)

data Expression = Expression
    { exprToken :: Token
    , exprKind :: ExpressionKind
    }
    deriving (Eq, Ord)

data ExpressionKind
    = RootExpr
        {rootLeaves :: [Expression]}
    | StructExpr
        { structName :: String
        , structConstructors :: [Expression]
        , structGenerics :: Maybe [Type]
        }
    | StructConstructorExpr
        { structConstructorName :: String
        , structConstructorFields :: [Expression]
        }
    | StructFieldExpr
        { structFieldName :: String
        , structFieldType :: Type
        }
    | FunctionExpr
        { functionName :: String
        , functionParams :: [(String, Type)]
        , functionReturnType :: Type
        , functionBody :: Expression
        }
    | ConstantBindingExpr
        { constantBindingName :: String
        , constantBindingType :: Type
        , constantBindingValue :: Expression
        }
    | FunctionParamExpr
        { fnParamName :: Maybe String
        , fnParamType :: Type
        }
    | BinaryOpExpr
        { binaryOpLeft :: Expression
        , binaryOpRight :: Expression
        , binaryOp :: BinaryOp
        }
    | PatternMatchExpr
        {patternMatchHandlers :: [Expression]}
    | NumberPatternExpr
        {numberPatternValue :: String}
    | VariablePatternExpr
        {variablePatternName :: String}
    | PatternHandlerExpr
        { patternHandlerPattern :: Expression
        , patternHandlerBody :: Expression
        }
    | NumberExpr
    | StringExpr String
    | TupleExpr [Expression]
    | BlockExpr
        {blockExpressions :: [Expression]}
    | FunctionCallExpr
        { functionCallFn :: Expression
        , functionCallArg :: Expression
        }
    | ValueReferenceExpr
        {variableReferenceName :: String}
    | BoolExpr Bool
    | LetExpr
        { letName :: String
        , letValue :: Expression
        , letBody :: Expression
        }
    | TypeClassExpr
        { typeClassName :: String
        , typeClassGenerics :: [String]
        , typeClassMethods :: [Expression]
        }
    | TypeClassMethodExpr
        { typeClassFnName :: String
        , typeClassFnType :: Type
        }
    | LambdaExpr
        { lambdaParams :: [String]
        , lambdaBody :: Expression
        }
    | ArrayExpr [Expression]
    deriving (Eq, Ord)

exprChildren :: ExpressionKind -> [Expression]
exprChildren (RootExpr leaves) = leaves
exprChildren (FunctionExpr _ _ _ body) = [body]
exprChildren (ConstantBindingExpr _ _ value) = [value]
exprChildren (FunctionParamExpr _ _) = []
exprChildren (BinaryOpExpr left right _) = [left, right]
exprChildren (PatternMatchExpr patterns) = patterns
exprChildren (NumberPatternExpr _) = []
exprChildren (VariablePatternExpr _) = []
exprChildren (PatternHandlerExpr pattern handler) = [pattern, handler]
exprChildren (NumberExpr) = []
exprChildren (FunctionCallExpr fn arg) = [fn, arg]
exprChildren (ValueReferenceExpr _) = []
exprChildren (StringExpr _) = []
exprChildren (TupleExpr expressions) = expressions
exprChildren (LetExpr _ value body) = [value, body]
exprChildren (BlockExpr expressions) = expressions
exprChildren (StructExpr _ constructors _) = constructors
exprChildren (StructConstructorExpr _ fields) = fields
exprChildren (StructFieldExpr _ _) = []
exprChildren (BoolExpr _) = []
exprChildren (TypeClassExpr _ _ methods) = methods
exprChildren (TypeClassMethodExpr _ _) = []
exprChildren (LambdaExpr _ body) = [body]
exprChildren (ArrayExpr expressions) = expressions

instance Show ExpressionKind where
    show :: ExpressionKind -> String
    show (RootExpr _) = "RootExpr"
    show (ConstantBindingExpr name _ _) = "ConstantBindingExpr (" ++ name ++ ")"
    show (FunctionExpr name params returnType _) = "FunctionExpr (" ++ name ++ " :: " ++ show params ++ " -> " ++ show returnType ++ ")"
    show (FunctionParamExpr name paramType) = "FunctionParamExpr (" ++ show name ++ " :: " ++ show paramType ++ ")"
    show (BinaryOpExpr left right operator) = "BinaryOpExpr (" ++ show left ++ " " ++ show operator ++ " " ++ show right ++ ")"
    show (PatternMatchExpr _) = "PatternMatchExpr"
    show (NumberPatternExpr value) = "NumberPatternExpr (" ++ value ++ ")"
    show (VariablePatternExpr name) = "VariablePatternExpr (" ++ name ++ ")"
    show (PatternHandlerExpr pattern _) = "PatternHandlerExpr (" ++ show pattern ++ ")"
    show (NumberExpr) = "NumberExpr"
    show (FunctionCallExpr fn arg) = "FunctionCallExpr (" ++ show fn ++ " " ++ show arg ++ ")"
    show (ValueReferenceExpr name) = "ValueReferenceExpr (" ++ name ++ ")"
    show (BlockExpr _) = "BlockExpr"
    show (TupleExpr expressions) = "TupleExpr (" ++ show expressions ++ ")"
    show (LetExpr name value body) = "LetExpr (" ++ name ++ " = " ++ show value ++ " in " ++ show body ++ ")"
    show (StringExpr value) = "StringExpr (" ++ value ++ ")"
    show (StructExpr name constructors generics) = "StructExpr (" ++ name ++ " :: " ++ show constructors ++ " :: " ++ show generics ++ ")"
    show (StructConstructorExpr name fields) = "StructConstructorExpr (" ++ name ++ " :: " ++ show fields ++ ")"
    show (StructFieldExpr name fieldType) = "StructFieldExpr (" ++ name ++ " :: " ++ show fieldType ++ ")"
    show (BoolExpr value) = "BoolExpr (" ++ show value ++ ")"
    show (TypeClassExpr name generics methods) = "TypeClassExpr (" ++ name ++ " :: " ++ show generics ++ " :: " ++ show methods ++ ")"
    show (TypeClassMethodExpr name _) = "TypeClassMethodExpr (" ++ name ++ ")"
    show (LambdaExpr params body) = "LambdaExpr (" ++ show params ++ " -> " ++ show body ++ ")"
    show (ArrayExpr expressions) = "ArrayExpr (" ++ show expressions ++ ")"

instance Show Expression where
    show (Expression token kind) = (show kind) ++ " '" ++ tokenValue token ++ "'"
