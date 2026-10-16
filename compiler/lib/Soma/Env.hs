module Soma.Env where

import Data.HashMap.Strict qualified as HM
import Soma.File (SourceFile)
import Symbolize (Symbol)

data ItemKind
    = ItemDef
    | ItemInduct
    | ItemConstructor

data ItemId = ItemId
    { itemFile :: !SourceFile
    , itemName :: !Symbol
    , itemKind :: !ItemKind
    , itemParent :: Maybe ItemId
    }

data Namespace = Namespace
    { nsDecls :: !(HM.HashMap Symbol ItemId)
    , nsChildren :: !(HM.HashMap Symbol Namespace)
    }

walk :: Namespace -> [Symbol] -> Maybe Namespace
walk current [] = Just current
walk current (x : xs) = do
    next <- HM.lookup x (nsChildren current)
    walk next xs

resolveItem :: Namespace -> [Symbol] -> Symbol -> Maybe ItemId
resolveItem ns path member = (HM.lookup member . nsDecls) =<< walk ns path
