module Soma.Elaborator.Decl where

import Data.Foldable (foldrM)
import Soma.Calculus
import Soma.Elaborator.Core (Decl (Decl, declSyntax), Elab)
import Soma.Elaborator.Expr (checkExpr, checkType, elabMaybeType, inferExpr)
import Soma.Syntax.Tree (Annotation (Annotated), Binder, binderAnnotation, defBinders, defBody, defType)

elabSig :: Decl -> Elab Term
elabSig Decl{declSyntax} = do
    res <- elabMaybeType $ defType declSyntax
    foldrM
        (\x acc -> (`TPi` acc) <$> elabBinder x)
        res
        (defBinders declSyntax)

elabBinder :: Binder -> Elab Term
elabBinder binder | (Annotated (Just ann)) <- binderAnnotation binder = checkType ann
elabBinder _ = pure type0

inferDecl :: Decl -> Elab (Term, Term)
inferDecl d@Decl{declSyntax} = do
    maybe ((TError,) <$> elabSig d) inferExpr (defBody declSyntax)

checkBody :: Decl -> Term -> Elab Term
checkBody Decl{declSyntax} sig =
    case defBody declSyntax of
        Nothing -> pure TError
        Just t -> checkExpr t sig
