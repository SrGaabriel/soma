{-# LANGUAGE DeriveGeneric #-}

module Metal.Metadata where

import GHC.Generics (Generic)
import Typing.Types (Constraint, QualifiedType, TyVar, Type)

data MetallicConstructorMetadata = MetallicConstructorMetadata
    { mcmTypeName :: String
    , mcmTag :: Int
    , mcmFields :: [Type]
    }
    deriving (Show, Eq)

data MetallicTypeClassMetadata = MetallicTypeClassMetadata
    { mtcName :: String
    , mtcMethods :: [(String, QualifiedType)]
    }
    deriving (Generic, Show, Eq)

data MetallicFunctionMetadata = MetallicFunctionMetadata
    { mfmOriginalName :: [TyVar]
    , mfmConstraints :: [Constraint]
    , mfmInstanceInfo :: Maybe MetallicInstanceInfo
    , mfmClosureInfo :: Maybe ClosureFunctionInfo
    , mfmIsInline :: Bool
    }
    deriving (Show, Eq)

newtype ClosureFunctionInfo = ClosureFunctionInfo
    { cfiCapturedVars :: [(String, Type)]
    }
    deriving (Show, Eq)

data MetallicInstanceInfo = InstanceInfo
    { iiClassName :: String
    , iiInstanceType :: String
    , iiMethodName :: String
    }
    deriving (Show, Eq)