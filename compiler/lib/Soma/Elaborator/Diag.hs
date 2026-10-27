{-# LANGUAGE OverloadedStrings #-}

module Soma.Elaborator.Diag where

import Maple.Ast (AstNode (syntax), AstToken (syntaxToken))
import Maple.Red (RedNode (rnRange), RedToken (rtRange))
import Soma.Diagnostic (Diagnostic, Label (Label, labFile, labMessage, labRange), Severity (SError), mkDiag, withHelps)
import Soma.Elaborator.Core (Decl (Decl, declFile, declSyntax))
import Soma.Syntax.Tree (defName, identText)

needsSignature :: Decl -> Diagnostic
needsSignature Decl{declFile, declSyntax} =
    withHelps ["add a type signature to `" <> name <> "`"] $
        mkDiag SError ("cannot infer the type of `" <> name <> "` because it is used recursively") $
            Label{labFile = declFile, labRange = range, labMessage = "used recursively"}
  where
    ident = defName declSyntax
    name = maybe "this definition" identText ident
    range = maybe (rnRange (syntax declSyntax)) (rtRange . syntaxToken) ident
