module Soma.Elaborator.Core where

import Control.Monad.State.Strict (MonadIO (liftIO), StateT, gets)
import Control.Monad.Writer.Strict (WriterT)
import Data.IORef (IORef, readIORef, writeIORef)
import Soma.Diagnostic (Diagnostic)
import Soma.Env (Item, Namespace)
import Soma.Unique (Unique (Unique), UniqueMap)

data ElabState = ElabState
    { elabUniqueRef :: IORef Unique
    , elabNamespace :: Namespace
    , elabItems :: !(UniqueMap Item)
    }

type Elab = WriterT [Diagnostic] (StateT ElabState IO)

mkUnique :: Elab Unique
mkUnique = do
    st <- gets elabUniqueRef
    Unique i <- liftIO $ readIORef st
    let new = Unique $ i + 1
    liftIO $ writeIORef st new
    pure new
