module Soma.Elaborator.Reduce where

import Control.Monad ((<=<))
import Control.Monad.State.Strict (gets)
import Data.Maybe (fromMaybe)
import Soma.Calculus (Term (TConst, TApp, TLam))
import Soma.Elaborator.Core (Elab, ElabState (elabItems))
import Soma.Env (Item (itemBody))
import Soma.Unique qualified as U

-- todo: subst
whnf :: Term -> Elab Term
whnf t@(TConst termId) =
    gets $ fromMaybe t . (itemBody <=< U.lookup termId) . elabItems
whnf (TApp (TLam param body) arg) = pure body
whnf o = pure o
