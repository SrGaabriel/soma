{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Soma.Elaborator.Context where

import Data.List (find)
import Soma.Calculus (Term)
import Soma.Unique (Unique)
import Soma.Unique qualified as U
import Symbolize (Symbol)

data Local = Local
    { localUnique :: !Unique
    , localName :: !(Maybe Symbol)
    , localType :: !Term
    , localValue :: !(Maybe Term)
    }

newtype LocalCtx = LocalCtx {locals :: U.UniqueMap Local}

resolveLocal :: LocalCtx -> Symbol -> Maybe Local
resolveLocal lcx sym =
    find
        (\Local{localName = (Just name)} -> name == sym)
        ([l | l@Local{localName = (Just _)} <- U.elems (locals lcx)])

data Meta
    = MUnsolved !Term !LocalCtx
    | MSolved !Term !Term

newtype MetaCtx = MetaCtx {metas :: U.UniqueMap Meta}
