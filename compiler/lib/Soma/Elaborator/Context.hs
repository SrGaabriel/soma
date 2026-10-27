module Soma.Elaborator.Context where

import Soma.Calculus (Term)
import Soma.Unique (UniqueMap)
import Symbolize (Symbol)

data Local = Local
    { localName :: !(Maybe Symbol)
    , localType :: !Term
    , localValue :: !(Maybe Term)
    }

newtype LocalCtx = LocalCtx {locals :: UniqueMap Local}

data Meta
    = Unsolved !Term !LocalCtx
    | Solved !Term !Term

newtype MetaCtx = MetaCtx {metas :: UniqueMap Meta}
