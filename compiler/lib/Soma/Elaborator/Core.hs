module Soma.Elaborator.Core where

import Control.Monad.State.Strict (MonadIO (liftIO), StateT, gets)
import Data.IORef (IORef, readIORef, writeIORef)
import Soma.Diagnostic (Diagnostic)
import Soma.Env (Item, Namespace)
import Soma.Unique (Unique (Unique), UniqueMap)
import Soma.Elaborator.Context (MetaCtx)

data ElabState = ElabState
    { elabUniqueRef :: IORef Unique
    , elabNamespace :: Namespace
    , elabItems :: !(UniqueMap Item)
    , elabMetas :: MetaCtx
    , elabErrors :: [Diagnostic]
    }

type Elab = StateT ElabState IO

mkUnique :: Elab Unique
mkUnique = do
    st <- gets elabUniqueRef
    Unique i <- liftIO $ readIORef st
    let new = Unique $ i + 1
    liftIO $ writeIORef st new
    pure new
