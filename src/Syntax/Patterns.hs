module Syntax.Patterns where
import Lexing.Position (Span)

data Literal
    = LitInt Int
    | LitString String
    | LitBool Bool
    deriving (Show, Eq, Ord)

data Pattern
    = PVar String Span -- variable
    | PWildcard Span -- _
    | PLit Literal Span -- (42, "hello", True)
    | PConstructor String [Pattern] Span -- (Circle x)
    | PTuple [Pattern] Span -- (x, y, z)
    | PArray [Pattern] Span -- [x, y, z]
    | PAs String Pattern Span -- shape@(Circle x)
    deriving (Show, Eq, Ord)
