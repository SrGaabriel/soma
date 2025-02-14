module Parsing.Type (Type(..)) where

data Type
    = IntType
    | StringType
    | BoolType
    | TupleType [Type]
    | FunctionType
        { functionTypeArgs :: [Type]
        , functionTypeReturn :: Type
        }
    | UnknownType String
    deriving (Show, Eq, Ord)
