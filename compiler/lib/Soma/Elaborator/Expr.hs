module Soma.Elaborator.Expr where

import Soma.Calculus
import Soma.Elaborator.Core (Elab)
import Soma.Syntax.Tree (Expr (..), Type, numberText, strLitValue)

checkExpr :: Expr -> Term -> Elab Term
checkExpr e _ = elabExpr e -- todo

elabExpr :: Expr -> Elab Term
elabExpr (EStrLit lit) = pure $ TLit $ LStr $ strLitValue lit
elabExpr (ENumLit lit) = pure $ TLit $ LNum $ numberText lit

inferExpr :: Expr -> Elab (Term, Term)
inferExpr = error "todo"

elabType :: Type -> Elab Term
elabType _ = pure type0 -- todo

elabMaybeType :: Maybe Type -> Elab Term
elabMaybeType (Just t) = elabType t
elabMaybeType Nothing = pure TError
