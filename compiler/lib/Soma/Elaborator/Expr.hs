module Soma.Elaborator.Expr where

import Soma.Calculus
import Soma.Elaborator.Core (Elab, lookupName, report)
import Soma.Elaborator.Diag (unknownName)
import Soma.Syntax.Tree (Expr (..), Name (Name), Type, identText, numberText, strLitValue)
import Symbolize (intern)

checkExpr :: Expr -> Term -> Elab Term
checkExpr e _ = elabExpr e -- todo

elabExpr :: Expr -> Elab Term
elabExpr (EStrLit lit) = pure $ TLit $ LStr $ strLitValue lit
elabExpr (ENumLit lit) = pure $ TLit $ LNum $ numberText lit
elabExpr (EVar var) = do
    name <- resolveName var
    pure name

inferExpr :: Expr -> Elab (Term, Term)
inferExpr = error "todo"

elabType :: Type -> Elab Term
elabType _ = pure type0 -- todo

elabMaybeType :: Maybe Type -> Elab Term
elabMaybeType (Just t) = elabType t
elabMaybeType Nothing = pure TError

resolveName :: Name -> Elab Term
resolveName name@(Name path member) = do
    let sPath = map (intern . identText) path
    let sMember = (intern . identText) member
    mTerm <- lookupName sPath sMember
    case mTerm of
        Just term -> pure term
        Nothing -> TError <$ report (unknownName name)
