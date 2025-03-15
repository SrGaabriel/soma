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
    deriving (Show, Eq, Ord)

data TypeVar = TypeVar String Int
  deriving (Show, Eq, Ord)