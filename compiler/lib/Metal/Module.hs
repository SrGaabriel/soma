module Metal.Module where

import Metal.Function
import Metal.Metadata (MetallicTypeClassMetadata)
import Typing.Types

data MetallicModule = MetallicModule
    { mmName :: String
    , mmFunctions :: [MetallicFunction]
    , mmTypes :: [MetallicTypeDef]
    , mmInstances :: [MetallicInstance]
    , mmTypeClasses :: [MetallicTypeClassMetadata]
    -- , metalExterns :: [MetallicExtern]
    }
    deriving (Show, Eq)

data MetallicTypeDef
    = MAlgebraicType
        { mtName :: String
        , mtConstructors :: [MetallicConstructor]
        }
    | MRecordType
        { mrName :: String
        , mrFields :: [(String, Type)]
        }
    deriving (Show, Eq)

data MetallicConstructor = MetallicConstructor
    { mcName :: String
    , mcTag :: Int
    , mcFields :: [Type]
    }
    deriving (Show, Eq)

data MetallicInstance = MetallicInstance
    { miClassName :: String
    , miInstanceType :: Type
    , miMethods :: [MetallicFunction]
    }
    deriving (Show, Eq)
