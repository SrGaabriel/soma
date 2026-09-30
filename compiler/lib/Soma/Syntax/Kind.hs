{-# LANGUAGE DeriveAnyClass #-}

module Soma.Syntax.Kind where

import Data.Data (Data)
import Maple.Ast (SyntaxKind (toRaw))
import Maple.Green (RawKind)

data Kind
    = -- Tokens
      KEof
    | KNumber
    | KStar
    | KUnknown
    | -- Nodes
      KRoot
    | KMul
    deriving (Eq, Show, Enum, Data)
    deriving anyclass (SyntaxKind)

tRoot, tEof, tNumber, tStar, tUnknown :: RawKind
tRoot = toRaw KRoot
tEof = toRaw KEof
tNumber = toRaw KNumber
tStar = toRaw KStar
tUnknown = toRaw KUnknown
