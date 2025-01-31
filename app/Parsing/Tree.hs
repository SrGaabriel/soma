{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}

module Parsing.Tree where

import Lexing.Lexer (Token)

class Expression a where
  token :: a -> Token
  children :: a -> [SomeExpr]

data SomeExpr = forall a. Expression a => SomeExpr (a)

data RootExpr = RootExpr Token [SomeExpr]

instance Expression RootExpr where
    token (RootExpr t _) = t
    children (RootExpr _ c) = c