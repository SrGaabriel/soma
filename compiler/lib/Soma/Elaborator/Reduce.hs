module Soma.Elaborator.Reduce where

import Control.Monad ((<=<))
import Control.Monad.State.Strict (gets)
import Soma.Calculus
import Soma.Elaborator.Core (Elab, ElabState (elabItems))
import Soma.Elaborator.Subst (instantiate)
import Soma.Env (Item (itemBody))
import Soma.Unique qualified as U

-- todo: subst
whnf :: Term -> Elab Term
whnf t@(TConst termId) =
    gets (itemBody <=< U.lookup termId . elabItems) >>= \case
        Just body -> whnf body
        Nothing -> pure t
whnf (TApp f a) =
    whnf f >>= \case
        TLam _ body -> whnf (instantiate body a)
        f' -> pure $ TApp f' a
whnf (TLet _ v body) = whnf (instantiate body v)
whnf t = pure t
