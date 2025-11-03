module Metal.Metadata where

import Typing.Types (Constraint, QualifiedType, TyVar, Type)

data MetallicConstructorMetadata = MetallicConstructorMetadata
    { mcmTypeName :: String
    , mcmTag :: Int
    , mcmFields :: [Type]
    }
    deriving (Show, Eq)

data MetallicTypeClassMetadata = MetallicTypeClassMetadata
    { mtcName :: String
    , mtcTypeVars :: [TyVar]
    , mtcMethods :: [(String, QualifiedType)]
    }
    deriving (Show, Eq)

data MetallicFunctionMetadata = MetallicFunctionMetadata
    { fmOriginalName :: [TyVar]
    , mfmConstraints :: [Constraint]
    , fmInstanceInfo :: Maybe MetallicInstanceInfo
    }
    deriving (Show, Eq)

data MetallicInstanceInfo = InstanceInfo
    { iiClassName :: String
    , iiInstanceType :: String
    , iiMethodName :: String
    }
    deriving (Show, Eq)
