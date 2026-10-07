{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}

module Soma.Syntax.Kind where

import Data.Data (Data)
import Data.Text (Text)
import Maple.Ast (SyntaxKind)
import Soma.Pretty (Pretty (pretty))

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
    deriving (Show, Eq, Enum, Data)
    deriving anyclass (SyntaxKind)

isTrivia :: Kind -> Bool
isTrivia KWhitespace = True
isTrivia KNewline = True
isTrivia _ = False

instance Pretty Kind where
    pretty :: Kind -> Text
    pretty KEof = "end of file"
    pretty KNumber = "number"
    pretty KStar = "'*'"
    pretty KDefKw = "'def'"
    pretty KIdent = "identifier"
    pretty KWhitespace = "whitespace"
    pretty KNewline = "newline"
    pretty KSemicolon = "';'"
    pretty KLParen = "'('"
    pretty KRParen = "')'"
    pretty KLBrace = "'{'"
    pretty KRBrace = "'}'"
    pretty KColon = "':'"
    pretty KColonEq = "':='"
    pretty KUnknown = "unknown"
    pretty KRoot = "root"
    pretty KMul = "multiplication"
    pretty KDef = "function definition"
