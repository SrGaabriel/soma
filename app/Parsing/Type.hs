module Parsing.Type (Type(..), TypeVar(..)) where

data Type
    = IntType
    | StringType
    | BoolType
    | TupleType [Type]
    | FunctionType
        { functionTypeArgs :: [Type]
        , functionTypeReturn :: Type
        }
    | UnresolvedStructType String
    | VarType TypeVar
    | ForAll [TypeVar] Type
    deriving (Eq, Ord)

data TypeVar = TypeVar String Int
  deriving (Show, Eq, Ord)

instance Show Type where
    show IntType = "Int"
    show StringType = "String"
    show BoolType = "Bool"
    show (TupleType ts) = "(" ++ unwords (map show ts) ++ ")"
    show (FunctionType args ret) = "(" ++ unwords (map show args) ++ " -> " ++ show ret ++ ")"
    show (UnresolvedStructType n) = n
    show (VarType v) = show v
    show (ForAll vars t) = "forall " ++ unwords (map show vars) ++ ". " ++ show t