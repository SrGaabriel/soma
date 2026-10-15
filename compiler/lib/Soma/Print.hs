module Soma.Print where

import Blammo.Logging (MonadLogger (monadLoggerLog))
import Control.Monad.State.Strict
import Data.Text (Text)
import Maple.Builder (BuilderT)

class Pretty a where
    pretty :: a -> Text

instance (MonadLogger m) => MonadLogger (BuilderT m) where
    monadLoggerLog loc src lvl msg = lift (monadLoggerLog loc src lvl msg)
