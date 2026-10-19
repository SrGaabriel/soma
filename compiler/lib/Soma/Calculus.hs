module Soma.Calculus where

import Soma.Env (ItemId, Unique)

data Term
    = TMeta !Unique
    | TFree !Unique
    | TBound !Int
    | TConst !ItemId
    | TPi Term Term
    | TSigma Term Term
    | TApp Term Term
    | TLam Term Term
    | TLet Term Term Term
    | TError
