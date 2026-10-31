module Soma.Calculus where

import Soma.Unique (Unique)

data Level
    = LZero
    | LSucc !Level
    | LMax !Level !Level
    | LIMax !Level !Level
    deriving (Eq, Show)

type0 :: Term
type0 = TSort (LSucc LZero)

data Term
    = TMeta !Unique
    | TFree !Unique
    | TBound !Int
    | TSort !Level
    | TConst !Unique
    | TPi Term Term
    | TSigma Term Term
    | TApp Term Term
    | TLam Term Term
    | TLet Term Term Term
    | TError
    deriving (Show, Eq)
