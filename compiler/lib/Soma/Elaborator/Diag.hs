{-# LANGUAGE OverloadedStrings #-}

module Soma.Elaborator.Diag where

import Data.Text qualified as T
import Maple.Ast (syntaxSpan, syntaxTokenSpan)
import Soma.Diagnostic (Diagnostic, Label (Label, labMessage, labSpan), Severity (SError), mkDiag, withHelps)
import Soma.Elaborator.Core (Decl (Decl, declSyntax))
import Soma.Syntax.Tree (Name (Name), defName, identText, nameSpan)

unknownName :: Name -> Diagnostic
unknownName name@(Name path member) =
    mkDiag SError ("unknown name `" <> text <> "`") $
        Label{labSpan = nameSpan name, labMessage = "this name is not defined"}
  where
    text = T.intercalate "::" (map identText (path ++ [member]))

needsSignature :: Decl -> Diagnostic
needsSignature Decl{declSyntax} =
    withHelps ["add a type signature to `" <> name <> "`"] $
        mkDiag SError ("cannot infer the type of `" <> name <> "` because it is used recursively") $
            Label{labSpan = location, labMessage = "used recursively"}
  where
    ident = defName declSyntax
    name = maybe "this definition" identText ident
    location = maybe (syntaxSpan declSyntax) syntaxTokenSpan ident
