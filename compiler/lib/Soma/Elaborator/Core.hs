module Soma.Elaborator.Core where

import Soma.Env (Namespace)

data ElabState = ElabState
    { elabNamespace :: Namespace
    }
