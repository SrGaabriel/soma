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
    | KDef
    | KIdent
    | KWhitespace
    | KNewline
    | KSemicolon
    | KUnknown
    | -- Nodes
      KRoot
    | KMul
    deriving (Eq, Show, Enum, Data)
    deriving anyclass (SyntaxKind)

kRoot, kEof, kNumber, kStar, kDef, kIdent, kUnknown :: RawKind
kRoot = toRaw KRoot
kEof = toRaw KEof
kNumber = toRaw KNumber
kStar = toRaw KStar
kDef = toRaw KDef
kIdent = toRaw KIdent
kUnknown = toRaw KUnknown

isTrivia :: Kind -> Bool
isTrivia KWhitespace = True
isTrivia KNewline = True
isTrivia _ = False
