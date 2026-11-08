module Soma.Env where

import Data.HashMap.Strict qualified as HM
import Soma.File (FileId)
import Symbolize (Symbol)
import Soma.Unique (Unique)

data ItemKind
    = ItemDef
    | ItemInduct
    | ItemConstructor
    deriving (Show, Eq)

data Item = ItemId
    { itemUnique :: !Unique
    , itemFile :: !FileId
    , itemName :: !Symbol
    , itemKind :: !ItemKind
    , itemParent :: Maybe Unique
    }
    deriving (Show, Eq)

data Namespace = Namespace
    { nsDecls :: !(HM.HashMap Symbol Item)
    , nsChildren :: HM.HashMap Symbol Namespace
    }

walk :: Namespace -> [Symbol] -> Maybe Namespace
walk current [] = Just current
walk current (x : xs) = do
    next <- HM.lookup x (nsChildren current)
    walk next xs

resolveItem :: Namespace -> [Symbol] -> Symbol -> Maybe Item
resolveItem ns path member = (HM.lookup member . nsDecls) =<< walk ns path
