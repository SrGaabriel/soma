{-# LANGUAGE MultiParamTypeClasses #-}

module Metal.Function where

import Metal.Expr (TypedExpr)
import Metal.Metadata
import Typing.Types (Type)

data MetallicFunction = MetallicFunction
    { mfName :: String
    , mfParams :: [(String, Type)]
    , mfReturnType :: Type
    , mfBody :: TypedExpr
    , mfMetadata :: MetallicFunctionMetadata
    }
    deriving (Show, Eq)
