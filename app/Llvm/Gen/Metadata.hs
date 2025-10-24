module Llvm.Gen.Metadata where

import Data.Map (Map)
import Llvm.Types (LlvmType)
import Syntax.Tree (Expr)
import Typing.Types (QualifiedType, TyVar, Type)

data ConstructorMetadata = ConstructorMetadata
    { constructorMetadataTypeName :: String
    , constructorMetadataTag :: Int
    , constructorMetadataArgs :: [Type]
    , constructorMetadataFieldLlvmTypes :: [LlvmType]
    , constructorMetadataFieldOffsets :: [Int]
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

data PolymorphicFunctionMetadata = PolymorphicFunction
    { polyFuncName :: String
    , polyFuncType :: QualifiedType
    , polyFuncBody :: Expr
    }
    deriving (Show)

data ArrayRepr
    = StackArray Int LlvmType
    | SliceView LlvmType
    | HeapArary LlvmType
    deriving (Eq, Show)

data ArrayMetadata = ArrayMetadata
    { arrayRep :: ArrayRepr
    , arrayElementType :: Type
    , arrayKnownSize :: Int
    , arrayIsUnique :: Bool
    , arrayEscapes :: Bool
    }
    deriving (Show)
