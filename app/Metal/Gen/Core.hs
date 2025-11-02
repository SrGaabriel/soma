{-# LANGUAGE FlexibleContexts #-}

module Metal.Gen.Core where

import Control.Monad.Reader
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import Inference.Core (TypeMap)
import Metal.Expr
import Metal.Function (MetallicFunction)
import Metal.Metadata (MetallicConstructorMetadata)
import Syntax.Tree (Expr)
import Typing.Types (QualifiedType (Forall), Type)

data MetalGenEnv = MetalGenEnv
    { metalCurrentScope :: MetalScope
    , metalCurrentPackage :: String
    , metalTypeMap :: TypeMap
    , metalConstructors :: Map String MetallicConstructorMetadata
    }

data MetalGenState = MetalGenState
    { metalNextTmp :: Int
    , metalFunctions :: Map String MetallicFunction
    , metalTypes :: Map String MetallicTypeDef
    }

data MetalScope = MetalScope
    { scopeName :: String
    , scopeVars :: Map String Type
    , scopeParent :: Maybe MetalScope
    }

type MetalGen a = ReaderT MetalGenEnv (State MetalGenState) a

runMetalGen :: MetalGenEnv -> MetalGenState -> MetalGen a -> (a, MetalGenState)
runMetalGen env st action = runState (runReaderT action env) st

defaultMetalEnv :: String -> TypeMap -> MetalGenEnv
defaultMetalEnv packageName tyMap =
    MetalGenEnv
        { metalCurrentScope = MetalScope "global" Map.empty Nothing
        , metalCurrentPackage = packageName
        , metalTypeMap = tyMap
        , metalConstructors = Map.empty
        }

freshTmp :: (MonadState MetalGenState m) => m String
freshTmp = do
    n <- gets metalNextTmp
    modify $ \s -> s{metalNextTmp = n + 1}
    return $ "tmp_" ++ show n

withScope :: MetalScope -> MetalGen a -> MetalGen a
withScope newScope = local (\env -> env { metalCurrentScope = newScope })

addFunction :: String -> MetallicFunction -> MetalGen ()
addFunction name func =
    modify $ \s -> s{metalFunctions = Map.insert name func (metalFunctions s)}

addType :: String -> MetallicTypeDef -> MetalGen ()
addType name tyDef =
    modify $ \s -> s{metalTypes = Map.insert name tyDef (metalTypes s)}

lookupVar :: String -> MetalGen (Maybe Type)
lookupVar name = do
    scope <- asks metalCurrentScope
    return $ lookupInScope scope name
  where
    lookupInScope :: MetalScope -> String -> Maybe Type
    lookupInScope (MetalScope _ vars parent) n =
        case Map.lookup n vars of
            Just ty -> Just ty
            Nothing -> parent >>= \p -> lookupInScope p n

lookupConstructor :: String -> MetalGen MetallicConstructorMetadata
lookupConstructor name = do
    ctors <- asks metalConstructors
    case Map.lookup name ctors of
        Just meta -> return meta
        Nothing -> error $ "Constructor not found: " ++ name

getExprType :: Expr -> MetalGen Type
getExprType expr = do
    tyMap <- asks metalTypeMap
    case Map.lookup expr tyMap of
        Just (Forall _ _ ty) -> return ty
        Nothing -> error $ "Type not found for expression: " ++ show expr
