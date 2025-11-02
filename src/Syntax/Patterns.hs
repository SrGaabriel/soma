module Syntax.Patterns where

data Literal
    = LitInt Integer
    | LitString String
    | LitBool Bool
    deriving (Show, Eq, Ord)

data Pattern
    = PVar String -- variable
    | PWildcard -- _
    | PLit Literal -- (42, "hello", True)
    | PConstructor String [Pattern] -- (Circle x)
    | PTuple [Pattern] -- (x, y, z)
    | PArray [Pattern] -- [x, y, z]
    | PAs String Pattern -- shape@(Circle x)
    deriving (Show, Eq, Ord)
