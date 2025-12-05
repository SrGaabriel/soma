{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}

module Lexing.Position (Span (..), Located (..), dummySpan, spanBetween) where

import GHC.Generics (Generic)

type SourcePos = Int

data Span = Span SourcePos SourcePos
    deriving (Show, Eq, Ord, Generic)

data Located a = Located
    { lLocation :: Span
    , lValue :: a
    }
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- todo(magic-spans): remove workaround
dummySpan :: Span
dummySpan = Span (-1) (-1)

spanBetween :: Span -> Span -> Span
spanBetween (Span s1 _) (Span _ e2) = Span s1 e2
