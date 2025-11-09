module Alloy.Dictionary (
    DictInfo (..),
    DictKey (..),
    TypeClassDict (..),
) where

import Data.Map.Strict (Map)
import Typing.Types (Type)

data DictKey = DictKey
    { dkClassName :: String
    , dkType :: Type
    }
    deriving (Show, Eq, Ord)

data TypeClassDict = TypeClassDict
    { tcdClassName :: String
    , tcdForType :: Type
    , tcdMethods :: [(String, Type)]
    }
    deriving (Show, Eq)

data DictInfo = DictInfo
    { diDictionaries :: Map DictKey TypeClassDict
    , diTypeClassMethods :: Map String [String]
    , diInstanceFunctions :: Map String (String, Type)
    }
    deriving (Show, Eq)
