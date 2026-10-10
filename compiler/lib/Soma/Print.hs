module Soma.Print where

import Data.Text (Text)
import Blammo.Logging (MonadLogger (monadLoggerLog))
import Maple.Builder (BuilderT)
import Control.Monad.State.Strict

class Pretty a where
    pretty :: a -> Text

instance MonadLogger m => MonadLogger (BuilderT m) where
    monadLoggerLog loc src lvl msg = lift (monadLoggerLog loc src lvl msg)
