module Metal.Module where

import Metal.Function
import Typing.Types

data MetallicModule = MetallicModule
    { mmFunctions :: [MetallicFunction]
    , mmTypes :: [MetallicTypeDef]
    , mmInstances :: [MetallicInstance]
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
