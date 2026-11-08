module Soma.Elaborator.Expr where

import Soma.Calculus
import Soma.Elaborator.Core (Elab, lookupName, report)
import Soma.Elaborator.Diag (unknownName)
import Soma.Syntax.Tree (Expr (..), Name (Name), identText, numberText, strLitValue, appFn, appArgs)
import Symbolize (intern)

checkType :: Expr -> Elab Term
checkType = elabExpr -- todo checkExpr with Sort

checkExpr :: Expr -> Term -> Elab Term
checkExpr e _ = elabExpr e -- todo

elabExpr :: Expr -> Elab Term
elabExpr (EStrLit lit) = pure $ TLit $ LStr $ strLitValue lit
elabExpr (ENumLit lit) = pure $ TLit $ LNum $ numberText lit
elabExpr (EVar var) = resolveName var
elabExpr (EApp app) = do
    tf <- elabMaybeExpr (appFn app)
    args <- traverse elabExpr (appArgs app)
    pure $ foldl' TApp tf args

inferExpr :: Expr -> Elab (Term, Term)
inferExpr = error "todo"

elabMaybeExpr :: Maybe Expr -> Elab Term
elabMaybeExpr (Just t) = elabExpr t
elabMaybeExpr Nothing = pure TError

elabMaybeType :: Maybe Expr -> Elab Term
elabMaybeType (Just t) = checkType t
elabMaybeType Nothing = pure TError

resolveName :: Name -> Elab Term
resolveName name@(Name path member) = do
    let sPath = map (intern . identText) path
    let sMember = (intern . identText) member
    mTerm <- lookupName sPath sMember
    case mTerm of
        Just term -> pure term
        Nothing -> TError <$ report (unknownName name)
