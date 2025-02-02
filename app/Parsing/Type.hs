module Parsing.Type (Type(..)) where

data Type
    = IntType
    | StringType
    | BoolType
    | TupleType [Type]
    | UnknownType String
    deriving (Show, Eq)
