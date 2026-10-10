{-# LANGUAGE DerivingVia #-}

module Soma.Syntax.Tree where

import Maple.Ast
import Maple.Red (RedNode)
import Soma.Syntax.Kind

newtype RootNode = RootNode RedNode
    deriving (AstNode) via (OfKind 'KRoot)

newtype MulExpr = MulExpr RedNode
    deriving (AstNode) via (OfKind 'KMul)

newtype 