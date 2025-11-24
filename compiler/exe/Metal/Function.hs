{-# LANGUAGE MultiParamTypeClasses #-}

module Metal.Function where

import Metal.Expr (MetallicExpr)
import Metal.Metadata
import Typing.Types (Type)

data MetallicFunction = MetallicFunction
    { mfName :: String
    , mfParams :: [(String, Type)]
    , mfReturnType :: Type
    , mfBody :: MetallicExpr
    , mfMetadata :: MetallicFunctionMetadata
    }
    deriving (Show, Eq)
