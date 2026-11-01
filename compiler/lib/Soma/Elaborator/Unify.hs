module Soma.Elaborator.Unify where

import Soma.Calculus (Term)
import Soma.Elaborator.Core (Elab)

unify :: Term -> Term -> Elab Term
unify = error "todo"

isDefEq :: Term -> Term -> Elab Bool
isDefEq t1 t2 = do
    pure $ t1 == t2
