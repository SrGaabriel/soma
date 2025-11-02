{-# LANGUAGE LambdaCase #-}
module Metal.Gen.Entry where
import Syntax.Tree
import Metal.Gen.Core
import Metal.Module (MetallicModule (..))
import Control.Monad.State
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Metal.Gen.Binding (metallizeBinding)
import Metal.Gen.Extracts (groupInstanceMethods)
import Inference.Core (TypeMap)

metallizeModule :: String -> Expr -> MetalGen MetallicModule
metallizeModule _ root = do
    let topLevelMembers = exprChildren root
    
    sequence_
        $ mapMaybe
            ( \case
                binding@(ExprBindingDef{}) -> Just (metallizeBinding binding)
                -- datatype@(ExprDataTypeDef{}) -> Just (compileDataTypeDef datatype)
                -- typeclass@(ExprTypeClassDef{}) -> Just (compileTypeClassDef typeclass)
                -- instanc@(ExprInstanceDef{}) -> Just (compileInstanceDef instanc)
                _ -> Nothing
            )
            topLevelMembers

    funcs <- gets metalFunctions
    types <- gets metalTypes
    instances <- gets metalInstanceMethods
    
    pure MetallicModule
        { mmFunctions = Map.elems funcs
        , mmTypes = Map.elems types
        , mmInstances = groupInstanceMethods instances
        }

compileMetalModule :: String -> Expr -> TypeMap -> MetallicModule
compileMetalModule name root typeMap =
    let (metalModule, _) = runMetalGen (defaultMetalEnv name typeMap) defaultMetalState (metallizeModule name root)
    in metalModule