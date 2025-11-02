{-# LANGUAGE MultiParamTypeClasses #-}

module Metal.Function where

import Metal.Expr (MetallicExpr)
import Typing.Types (Constraint, TyVar, Type)

data MetallicFunction
    = MPolymorphic
        { mfName :: String
        , mfTypeParams :: [TyVar]
        , mfConstraints :: [Constraint]
        , mfParams :: [(String, Type)]
        , mfReturnType :: Type
        , mfBody :: MetallicExpr
        }
    | MMonomorphic
        { mfName :: String
        , mfParams :: [(String, Type)]
        , mfReturnType :: Type
        , mfBody :: MetallicExpr
        }
    | MInstanceMethod
        { mfName :: String
        , mfClassName :: String
        , mfInstanceType :: Type
        , mfTypeParams :: [TyVar]
        , mfConstraints :: [Constraint]
        , mfParams :: [(String, Type)]
        , mfReturnType :: Type
        , mfBody :: MetallicExpr
        }
    deriving (Show, Eq)
