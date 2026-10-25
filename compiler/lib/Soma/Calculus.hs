module Soma.Calculus where

import Soma.Unique (Unique)

data Term
    = TMeta !Unique
    | TFree !Unique
    | TBound !Int
    | TConst !Unique
    | TPi Term Term
    | TSigma Term Term
    | TApp Term Term
    | TLam Term Term
    | TLet Term Term Term
    | TError
    deriving (Show, Eq)
