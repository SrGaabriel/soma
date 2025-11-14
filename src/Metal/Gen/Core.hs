{-# LANGUAGE FlexibleContexts #-}

module Metal.Gen.Core where

import Control.Monad.Reader
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import Inference.Core (TypeMap)
import Metal.Function (MetallicFunction)
import Metal.Gen.Metadata (extractConstructorMetadata)
import Metal.Metadata (MetallicConstructorMetadata, MetallicTypeClassMetadata)
import Metal.Module (MetallicTypeDef)
import Syntax.Tree (Expr)
import Typing.Types (QualifiedType (Forall), Type)

data MetalGenEnv = MetalGenEnv
    { metalCurrentScope :: MetalScope
    , metalCurrentPackage :: String
    , metalModuleName :: String
    , metalTypeMap :: TypeMap
    , metalConstructors :: Map String MetallicConstructorMetadata
    }

data MetalGenState = MetalGenState
    { metalNextTmp :: Int
    , metalFunctions :: Map String MetallicFunction
    , metalTypes :: Map String MetallicTypeDef
    , metalInstanceMethods :: Map (String, Type, String) MetallicFunction
    , metalTypeClasses :: Map String MetallicTypeClassMetadata
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
        , metalModuleName = packageName
        , metalTypeMap = tyMap
        , metalConstructors = Map.empty
        }

envWithConstructorsFrom :: String -> TypeMap -> Expr -> Map String MetallicConstructorMetadata -> MetalGenEnv
envWithConstructorsFrom packageName tyMap root externalCtors =
    let localCtors = extractConstructorMetadata root
        allCtors = Map.union localCtors externalCtors
    in (defaultMetalEnv packageName tyMap)
           { metalConstructors = allCtors
           }

withConstructors :: Map String MetallicConstructorMetadata -> MetalGen a -> MetalGen a
withConstructors ctors = local (\env -> env{metalConstructors = ctors})

defaultMetalState :: MetalGenState
defaultMetalState =
    MetalGenState
        { metalNextTmp = 0
        , metalFunctions = Map.empty
        , metalTypes = Map.empty
        , metalInstanceMethods = Map.empty
        , metalTypeClasses = Map.empty
        }

freshTmp :: (MonadState MetalGenState m) => m String
freshTmp = do
    n <- gets metalNextTmp
    modify $ \s -> s{metalNextTmp = n + 1}
    pure $ "tmp_" ++ show n

withScope :: MetalScope -> MetalGen a -> MetalGen a
withScope newScope = local (\env -> env{metalCurrentScope = newScope})

addFunction :: String -> MetallicFunction -> MetalGen ()
addFunction name func =
    modify $ \s -> s{metalFunctions = Map.insert name func (metalFunctions s)}

addType :: String -> MetallicTypeDef -> MetalGen ()
addType name tyDef =
    modify $ \s -> s{metalTypes = Map.insert name tyDef (metalTypes s)}

addTypeClass :: String -> MetallicTypeClassMetadata -> MetalGen ()
addTypeClass name tcMeta =
    modify $ \s -> s{metalTypeClasses = Map.insert name tcMeta (metalTypeClasses s)}

lookupVar :: String -> MetalGen (Maybe Type)
lookupVar name = do
    scope <- asks metalCurrentScope
    let go :: MetalScope -> MetalGen (Maybe Type)
        go (MetalScope _ vars parent) =
            case Map.lookup name vars of
                Just ty -> pure (Just ty)
                Nothing -> case parent of
                    Just p -> go p
                    Nothing -> pure Nothing
    go scope

lookupConstructor :: String -> MetalGen MetallicConstructorMetadata
lookupConstructor name = do
    ctors <- asks metalConstructors
    case Map.lookup name ctors of
        Just meta -> pure meta
        Nothing -> error $ "Constructor not found: " ++ name

getExprType :: Expr -> MetalGen Type
getExprType expr = do
    tyMap <- asks metalTypeMap
    case Map.lookup expr tyMap of
        Just (Forall _ _ ty) -> pure ty
        Nothing -> error $ "Type not found for expression: " ++ show expr
