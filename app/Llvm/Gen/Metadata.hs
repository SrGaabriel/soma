module Llvm.Gen.Metadata where

import Data.Map (Map)
import Typing.Types (QualifiedType, TyVar, Type)

data ConstructorMetadata = ConstructorMetadata
    { constructorMetadataTypeName :: String
    , constructorMetadataTag :: Int
    , constructorMetadataArgs :: [Type]
    }
    deriving (Show, Eq)

data TypeClassMetadata = TypeClassMetadata
    { tcName :: String
    , tcTypeVars :: [TyVar]
    , tcMethods :: Map String QualifiedType
    }
    deriving (Show)

data InstanceMetadata = InstanceMetadata
    { instClassName :: String
    , instType :: Type
    }
    deriving (Show)
