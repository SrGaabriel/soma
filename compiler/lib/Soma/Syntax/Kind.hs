{-# LANGUAGE DeriveAnyClass #-}

module Soma.Syntax.Kind where

import Data.Data (Data)
import Maple.Ast (SyntaxKind)

data Kind
    = -- Tokens
      KEof
    | KNumber
    | KStar
    | KDefKw
    | KIdent
    | KWhitespace
    | KNewline
    | KSemicolon
    | KLParen
    | KRParen
    | KLBrace
    | KRBrace
    | KColon
    | KColonEq
    | KUnknown
    | -- Nodes
      KRoot
    | KMul
    | KDef
    deriving (Eq, Show, Enum, Data)
    deriving anyclass (SyntaxKind)

isTrivia :: Kind -> Bool
isTrivia KWhitespace = True
isTrivia KNewline = True
isTrivia _ = False
