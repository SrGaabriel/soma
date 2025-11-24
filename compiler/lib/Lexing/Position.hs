{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}

module Lexing.Position (Span (..)) where

import GHC.Generics (Generic)

type SourcePos = Int

data Span = Span SourcePos SourcePos
    deriving (Show, Eq, Ord, Generic)

data Located a = Located
    { location :: Span
    , value :: a
    }
    deriving (Show, Eq, Functor, Foldable, Traversable)
