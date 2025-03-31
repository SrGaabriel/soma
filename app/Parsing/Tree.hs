module Parsing.Tree (Expression (..), ExpressionKind (..), exprChildren) where

import qualified Data.Map as Map
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
        , functionParams :: Map.Map String Type
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
    deriving (Eq, Ord)

exprChildren :: ExpressionKind -> [Expression]
exprChildren kind = case kind of
    RootExpr leaves -> leaves
    FunctionExpr _ _ _ body -> [body]
    ConstantBindingExpr _ _ value -> [value]
    FunctionParamExpr _ _ -> []
    BinaryOpExpr left right _ -> [left, right]
    PatternMatchExpr patterns -> patterns
    NumberPatternExpr _ -> []
    VariablePatternExpr _ -> []
    PatternHandlerExpr pattern handler -> [pattern, handler]
    NumberExpr -> []
    FunctionCallExpr fn arg -> [fn, arg]
    ValueReferenceExpr _ -> []
    StringExpr _ -> []
    TupleExpr expressions -> expressions
    LetExpr _ value body -> [value, body]
    BlockExpr expressions -> expressions
    StructExpr _ constructors _ -> constructors
    StructConstructorExpr _ fields -> fields
    StructFieldExpr _ _ -> []
    BoolExpr _ -> []
    TypeClassExpr _ _ methods -> methods
    TypeClassMethodExpr _ _ -> []

instance Show ExpressionKind where
    show kind = case kind of
        RootExpr _ -> "RootExpr"
        ConstantBindingExpr name _ _ -> "ConstantBindingExpr (" ++ name ++ ")"
        FunctionExpr name params returnType _ -> "FunctionExpr (" ++ name ++ " :: " ++ show params ++ " -> " ++ show returnType ++ ")"
        FunctionParamExpr name paramType -> "FunctionParamExpr (" ++ show name ++ " :: " ++ show paramType ++ ")"
        BinaryOpExpr left right operator -> "BinaryOpExpr (" ++ show left ++ " " ++ show operator ++ " " ++ show right ++ ")"
        PatternMatchExpr _ -> "PatternMatchExpr"
        NumberPatternExpr value -> "NumberPatternExpr (" ++ value ++ ")"
        VariablePatternExpr name -> "VariablePatternExpr (" ++ name ++ ")"
        PatternHandlerExpr pattern _ -> "PatternHandlerExpr (" ++ show pattern ++ ")"
        NumberExpr -> "NumberExpr"
        FunctionCallExpr fn arg -> "FunctionCallExpr (" ++ show fn ++ " " ++ show arg ++ ")"
        ValueReferenceExpr name -> "ValueReferenceExpr (" ++ name ++ ")"
        BlockExpr _ -> "BlockExpr"
        TupleExpr expressions -> "TupleExpr (" ++ show expressions ++ ")"
        LetExpr name value body -> "LetExpr (" ++ name ++ " = " ++ show value ++ " in " ++ show body ++ ")"
        StringExpr value -> "StringExpr (" ++ value ++ ")"
        StructExpr name constructors generics -> "StructExpr (" ++ name ++ " :: " ++ show constructors ++ " :: " ++ show generics ++ ")"
        StructConstructorExpr name fields -> "StructConstructorExpr (" ++ name ++ " :: " ++ show fields ++ ")"
        StructFieldExpr name fieldType -> "StructFieldExpr (" ++ name ++ " :: " ++ show fieldType ++ ")"
        BoolExpr value -> "BoolExpr (" ++ show value ++ ")"
        TypeClassExpr name generics methods -> "TypeClassExpr (" ++ name ++ " :: " ++ show generics ++ " :: " ++ show methods ++ ")"
        TypeClassMethodExpr name _ -> "TypeClassMethodExpr (" ++ name ++ ")"

instance Show Expression where
    show (Expression token kind) = (show kind) ++ " '" ++ tokenValue token ++ "'"
