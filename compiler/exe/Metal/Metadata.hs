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
    -- ^ If this function is a lifted lambda, contains info about captured vars
    , mfmIsInline :: Bool
    -- ^ Whether this function is marked with the inline modifier
    }
    deriving (Show, Eq)

{- | Info for lifted lambda functions (uniform closure calling convention)
Lifted lambdas take closure_self as first param and extract env from it
-}
newtype ClosureFunctionInfo = ClosureFunctionInfo
    { cfiCapturedVars :: [(String, Type)]
    {- ^ Variables captured from enclosing scope, in order
    These are extracted from closure_self at function entry
    -}
    }
    deriving (Show, Eq)

data MetallicInstanceInfo = InstanceInfo
    { iiClassName :: String
    , iiInstanceType :: String
    , iiMethodName :: String
    }
    deriving (Show, Eq)
