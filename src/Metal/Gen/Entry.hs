module Metal.Gen.Entry where

import Control.Monad.State (gets, modify)
import qualified Data.Map as Map

import Inference.Core (TypeMap)
import Metal.Function (MetallicFunction (..))
import Metal.Gen.Binding (metallizeBinding)
import Metal.Gen.Core (
    MetalGen,
    MetalGenState (..),
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
import Typing.Types (TyConstructor (..), Type (..))

metallizeModule :: String -> Expr -> MetalGen MetallicModule
metallizeModule _ root = do
    compileDataTypeDefsFromRoot root

    let topLevelMembers = exprChildren root
    mapM_ metallizeBinding [b | b@(ExprBindingDef{}) <- topLevelMembers]

    mapM_ metallizeInstance [inst | inst@(ExprInstanceDef{}) <- topLevelMembers]

    funcs <- gets metalFunctions
    types <- gets metalTypes
    instances <- gets metalInstanceMethods

    pure
        MetallicModule
            { mmFunctions = Map.elems funcs
            , mmTypes = Map.elems types
            , mmInstances = groupInstanceMethods instances
            }

metallizeInstance :: Expr -> MetalGen ()
metallizeInstance (ExprInstanceDef constraintType methods _) =
    mapM_ (metallizeInstanceMethod (extractInstanceTypeName constraintType)) methods
  where
    extractInstanceTypeName :: Type -> String
    extractInstanceTypeName (TApp _ ty) = extractInstanceTypeName ty
    extractInstanceTypeName (TConstructor (TypeConstructor name _)) = name
    extractInstanceTypeName u = error $ "Unexpected instance constraint type: " ++ show u

    metallizeInstanceMethod :: String -> Expr -> MetalGen ()
    metallizeInstanceMethod typeName bind@(ExprBindingDef name _ _ _ _) = do
        metallizeBinding bind
        let mangledName = name ++ "$" ++ typeName
        funcs <- gets metalFunctions
        case Map.lookup name funcs of
            Just func -> modify $ \s ->
                s
                    { metalFunctions =
                        Map.insert
                            mangledName
                            (func{mfName = mangledName})
                            (Map.delete name (metalFunctions s))
                    }
            Nothing -> pure ()
    metallizeInstanceMethod _ _ = pure ()
metallizeInstance _ = pure ()

compileMetalModule :: String -> Expr -> TypeMap -> MetallicModule
compileMetalModule name root typeMap =
    let env = envWithConstructorsFrom name typeMap root
        (metalModule, _) = runMetalGen env defaultMetalState (metallizeModule name root)
    in metalModule
