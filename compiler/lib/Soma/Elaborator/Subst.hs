module Soma.Elaborator.Subst where

import Soma.Calculus

instantiate :: Term -> Term -> Term
instantiate t t' = instantiateAt t t' 0

{- | If we want to apply a function to a term, we have to replace
the body's uses of De Bruijn indices

So for instance: (\x.\y. x + y) 5
Is equivalent to (\.\. i_1 + i_0) 5

We have to pass the De Bruijn level (not index) of what we're looking for since
instantiation is almost always done to the outermost binder

If we do it naively we get (\. i_1 + i_0)
But now i_1 is free and i_0 is never referenced.

So every time we go inside a binding, we add 1 to what we are looking for to
emulate De Bruijn indices, then the body (i_1 + i_0) becomes (5 + i_0)
-}
instantiateAt :: Term -> Term -> Int -> Term
instantiateAt b@(TBound bIdx) subst idx
    | bIdx == idx = subst
    | bIdx > idx = TBound $ bIdx - 1
    | otherwise = b
instantiateAt (TApp fn value) subst idx =
    TApp (instantiateAt fn subst idx) (instantiateAt value subst idx)
instantiateAt (TLam arg body) subst idx =
    TLam (instantiateAt arg subst idx) (instantiateAt body subst (idx + 1))
instantiateAt (TLet bind fn value) subst idx =
    TLet (instantiateAt bind subst idx) (instantiateAt fn subst idx) (instantiateAt value subst (idx + 1))
instantiateAt (TPi from to) subst idx =
    TPi (instantiateAt from subst idx) (instantiateAt to subst (idx + 1))
instantiateAt (TSigma f s) subst idx =
    TSigma (instantiateAt f subst idx) (instantiateAt s subst (idx + 1))
instantiateAt u _subst _idx = u

shift :: Term -> Int -> Term
shift term offset = shiftAt term 0 offset

shiftAt :: Term -> Int -> Int -> Term
shiftAt b@(TBound bIdx) idx offset
    | bIdx >= idx = TBound $ idx + offset
    | otherwise = b
shiftAt (TApp fn value) idx offset =
    TApp (shiftAt fn idx offset) (shiftAt value idx offset)
shiftAt (TLam arg body) idx offset =
    TLam (shiftAt arg idx offset) (shiftAt body (idx + 1) offset)
shiftAt (TLet bind fn value) idx offset =
    TLet (shiftAt bind idx offset) (shiftAt fn idx offset) (shiftAt value (idx + 1) offset)
shiftAt (TPi from to) idx offset =
    TPi (shiftAt from idx offset) (shiftAt to (idx + 1) offset)
shiftAt (TSigma f s) idx offset =
    TSigma (shiftAt f idx offset) (shiftAt s (idx + 1) offset)
shiftAt u _subst _idx = u
