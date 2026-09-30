{-# LANGUAGE DerivingVia #-}

module Soma.Syntax.Tree where

import Maple.Ast
import Maple.Red (RedNode)
import Soma.Syntax.Kind

newtype MulExpr = MulExpr RedNode
    deriving (AstNode) via (OfKind 'KMul)

newtype NumberExpr = NumberExpr RedNode
    deriving (AstNode) via (OfKind 'KNumber)
