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
    deriving (Eq, Enum, Data)
    deriving anyclass (SyntaxKind)

isTrivia :: Kind -> Bool
isTrivia KWhitespace = True
isTrivia KNewline = True
isTrivia _ = False

instance Show Kind where
    show KEof = "end of file"
    show KNumber = "number"
    show KStar = "'*'"
    show KDefKw = "'def'"
    show KIdent = "identifier"
    show KWhitespace = "whitespace"
    show KNewline = "newline"
    show KSemicolon = "';'"
    show KLParen = "'('"
    show KRParen = "')'"
    show KLBrace = "'{'"
    show KRBrace = "'}'"
    show KColon = "':'"
    show KColonEq = "':='"
    show KUnknown = "unknown"
    show KRoot = "root"
    show KMul = "multiplication"
    show KDef = "function definition"
