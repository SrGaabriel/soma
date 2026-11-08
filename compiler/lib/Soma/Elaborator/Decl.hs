module Soma.Elaborator.Decl where

import Data.Vector.Strict qualified as V
import Soma.Calculus
import Soma.Elaborator.Core (Decl (Decl, declSyntax), Elab)
import Soma.Elaborator.Expr (checkExpr, elabMaybeType, elabPis, inferExpr)
import Soma.Syntax.Tree (defBinders, defBody, defType)

elabSig :: Decl -> Elab Term
elabSig Decl{declSyntax} =
    elabPis (V.toList (defBinders declSyntax)) (elabMaybeType (defType declSyntax))

inferDecl :: Decl -> Elab (Term, Term)
inferDecl d@Decl{declSyntax} = do
    maybe ((TError,) <$> elabSig d) inferExpr (defBody declSyntax)

checkBody :: Decl -> Term -> Elab Term
checkBody Decl{declSyntax} sig =
    case defBody declSyntax of
        Nothing -> pure TError
        Just t -> checkExpr t sig
