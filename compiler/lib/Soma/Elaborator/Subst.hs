module Soma.Elaborator.Subst where

import Soma.Calculus
import Soma.Elaborator.Core (Elab)

instantiate :: Term -> Term -> Int -> Elab Term
instantiate b@(TBound bIdx) subst idx
    | bIdx == idx = pure subst
    | bIdx > idx = pure $ TBound $ bIdx - 1
    | otherwise = pure b
instantiate (TApp fn value) subst idx =
    (TApp <$> (instantiate fn subst idx)) <*> (instantiate value subst idx)
instantiate (TLam arg body) subst idx =
    (TLam <$> (instantiate arg subst idx)) <*> (instantiate body subst (idx+1))
instantiate (TLet bind fn value) subst idx =
    (TLet <$> (instantiate bind subst idx)) <*> (instantiate fn subst idx) <*> (instantiate value subst (idx+1))
instantiate (TPi from to) subst idx =
    (TPi <$> (instantiate from subst idx)) <*> (instantiate to subst (idx+1))
instantiate (TSigma f s) subst idx =
    (TSigma <$> (instantiate f subst idx)) <*> (instantiate s subst (idx+1))
instantiate u _subst _idx = pure u
