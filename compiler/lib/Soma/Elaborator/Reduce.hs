module Soma.Elaborator.Reduce where

import Soma.Calculus
import Soma.Elaborator.Core (Elab, unfoldConst)
import Soma.Elaborator.Subst (instantiate)

-- todo: subst
whnf :: Term -> Elab Term
whnf t@(TConst termId) =
    unfoldConst termId >>= \case
        Just body -> whnf body
        Nothing -> pure t
whnf (TApp f a) =
    whnf f >>= \case
        TLam _ body -> whnf (instantiate body a)
        f' -> pure $ TApp f' a
whnf (TLet _ v body) = whnf (instantiate body v)
whnf t = pure t
