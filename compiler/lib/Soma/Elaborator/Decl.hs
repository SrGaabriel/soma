module Soma.Elaborator.Decl where

import Soma.Calculus
import Soma.Elaborator.Core (Decl (Decl, declSyntax), Elab)
import Soma.Elaborator.Expr (checkExpr, elabBinder, elabMaybeType, inferExpr)
import Soma.Syntax.Tree (defBinders, defBody, defType)

elabSig :: Decl -> Elab Term
elabSig Decl{declSyntax} = do
    res <- elabMaybeType $ defType declSyntax
    bs <- traverse elabBinder (defBinders declSyntax)
    pure $ foldr (uncurry TPi) res bs

inferDecl :: Decl -> Elab (Term, Term)
inferDecl d@Decl{declSyntax} = do
    maybe ((TError,) <$> elabSig d) inferExpr (defBody declSyntax)

checkBody :: Decl -> Term -> Elab Term
checkBody Decl{declSyntax} sig =
    case defBody declSyntax of
        Nothing -> pure TError
        Just t -> checkExpr t sig
