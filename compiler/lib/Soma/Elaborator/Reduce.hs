module Soma.Elaborator.Reduce where

import Control.Monad.State.Strict (gets)
import Soma.Calculus
import Soma.Elaborator.Context (Meta (MSolved), MetaCtx (metas))
import Soma.Elaborator.Core (DeclState (declMetas), Elab, unfoldConst)
import Soma.Elaborator.Subst (instantiate)
import Soma.Unique qualified as U

whnf :: Term -> Elab Term
whnf t@(TConst termId) =
    unfoldConst termId >>= \case
        Just body -> whnf body
        Nothing -> pure t
whnf (TApp f a) =
    whnf f >>= \case
        TLam _ body -> whnf (instantiate body a)
        f' -> pure $ TApp f' a
whnf (TLet _ value body) = whnf (instantiate body value)
whnf m@(TMeta mvar) =
    gets (U.lookup mvar . metas . declMetas) >>= \case
        Just (MSolved _ value) -> whnf value
        _ -> pure m
whnf t = pure t
