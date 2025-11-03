{-# LANGUAGE LambdaCase #-}

module Metal.Gen.Entry where

import Control.Monad.State (gets)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)

import Inference.Core (TypeMap)
import Metal.Gen.Binding (metallizeBinding)
import Metal.Gen.Core (
    MetalGen,
    defaultMetalState,
    envWithConstructorsFrom,
    metalFunctions,
    metalInstanceMethods,
    metalTypes,
    runMetalGen,
 )
import Metal.Gen.DataTypes (compileDataTypeDefsFromRoot)
import Metal.Gen.Extracts (groupInstanceMethods)
import Metal.Module (MetallicModule (..))
import Syntax.Tree (Expr (..), exprChildren)

metallizeModule :: String -> Expr -> MetalGen MetallicModule
metallizeModule _ root = do
    compileDataTypeDefsFromRoot root

    let topLevelMembers = exprChildren root
    sequence_
        $ mapMaybe
            ( \case
                binding@(ExprBindingDef{}) -> Just (metallizeBinding binding)
                _ -> Nothing
            )
            topLevelMembers

    funcs <- gets metalFunctions
    types <- gets metalTypes
    instances <- gets metalInstanceMethods

    pure
        MetallicModule
            { mmFunctions = Map.elems funcs
            , mmTypes = Map.elems types
            , mmInstances = groupInstanceMethods instances
            }

compileMetalModule :: String -> Expr -> TypeMap -> MetallicModule
compileMetalModule name root typeMap =
    let env = envWithConstructorsFrom name typeMap root
        (metalModule, _) = runMetalGen env defaultMetalState (metallizeModule name root)
    in metalModule
