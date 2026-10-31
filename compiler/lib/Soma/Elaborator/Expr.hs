module Soma.Elaborator.Expr where

import Soma.Calculus
import Soma.Elaborator.Core (Elab)
import Soma.Syntax.Tree (Expr, Type)

checkExpr :: Expr -> Term -> Elab Term
checkExpr = error "todo"

elabExpr :: Expr -> Elab Term
elabExpr = error "todo"

inferExpr :: Expr -> Elab (Term, Term)
inferExpr = error "todo"

elabType :: Type -> Elab Term
elabType = error "todo"

elabMaybeType :: Maybe Type -> Elab Term
elabMaybeType (Just t) = elabType t
elabMaybeType Nothing = pure TError
