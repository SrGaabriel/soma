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

-- | Function attributes extracted from source-level @[...] annotations
data FunctionAttributes = FunctionAttributes
    { faInline :: !Bool
    -- ^ @[inline] - hint to inline
    , faNoInline :: !Bool
    -- ^ @[noinline] - prevent inlining
    , faDeprecated :: !(Maybe String)
    -- ^ @[deprecated "msg"]
    , faExtern :: !(Maybe String)
    -- ^ @[extern "c_name"]
    }
    deriving (Generic, Show, Eq)

defaultFunctionAttributes :: FunctionAttributes
defaultFunctionAttributes =
    FunctionAttributes
        { faInline = False
        , faNoInline = False
        , faDeprecated = Nothing
        , faExtern = Nothing
        }

data MetallicFunctionMetadata = MetallicFunctionMetadata
    { mfmTypeVars :: [TyVar]
    , mfmConstraints :: [Constraint]
    , mfmInstanceInfo :: Maybe MetallicInstanceInfo
    , mfmClosureInfo :: Maybe ClosureFunctionInfo
    , mfmAttributes :: FunctionAttributes
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
