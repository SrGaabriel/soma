{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}

module Lexing.Position (Span (..)) where

type SourcePos = Int

data Span = Span SourcePos SourcePos
    deriving (Show, Eq, Ord)

data Located a = Located
    { location :: Span
    , value :: a
    }
    deriving (Show, Eq, Functor, Foldable, Traversable)
