{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
module Lexing.Position where

type SourcePos = Int

data Span = Span SourcePos SourcePos
  deriving (Show, Eq, Ord)

data Located a = Located
  { location :: Span
  , value    :: a
  } deriving (Show, Eq, Functor, Foldable, Traversable)