{-# LANGUAGE MultiParamTypeClasses #-}

module Metal.Function where

import Metal.Expr (TypedExpr)
import Metal.Metadata
import Project.Name (Name)
import Typing.Types (Type)

data MetallicFunction = MetallicFunction
    { mfName :: Name
    , mfParams :: [(Name, Type)]
    , mfReturnType :: Type
    , mfBody :: TypedExpr
    , mfMetadata :: MetallicFunctionMetadata
    }
    deriving (Show, Eq)
