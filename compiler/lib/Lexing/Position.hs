{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}

module Lexing.Position (Span (..), Located (..), dummySpan) where

import GHC.Generics (Generic)

type SourcePos = Int

data Span = Span SourcePos SourcePos
    deriving (Show, Eq, Ord, Generic)

data Located a = Located
    { lLocation :: Span
    , lValue :: a
    }
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

dummySpan :: Span
dummySpan = Span (-1) (-1)
