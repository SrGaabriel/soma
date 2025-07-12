module Inference.Tree where

import Inference.Assembler (inferType)
import Inference.Core (ClassEnv, InstanceEnv, TypeEnv, TypeMap)
import Inference.Errors (InferenceError)
import Syntax.Tree (Expr (..), exprChildren)
import Typing.Types (Type (..), TyConstructor (..), Kind (..))
import qualified Data.Map as Map

analyzeTree :: TypeEnv -> ClassEnv -> InstanceEnv -> Expr -> Either [InferenceError] TypeMap
analyzeTree tEnv cEnv iEnv root = do
    case inferType tEnv cEnv iEnv root of
        Left err -> Left err
        Right (_rootType, typeMap) -> Right typeMap

analyzeTreeT :: TypeEnv -> Expr -> Either [InferenceError] TypeMap
analyzeTreeT tEnv root = do
    let cEnv = tEnv
    let iEnv = buildInstanceEnvironment root
    analyzeTree tEnv cEnv iEnv root

buildInstanceEnvironment :: Expr -> InstanceEnv
buildInstanceEnvironment root = foldl collectInstance Map.empty (collectInstances root)
  where
    collectInstances :: Expr -> [Expr]
    collectInstances expr = case expr of
        ExprRoot children -> concatMap collectInstances children
        inst@ExprInstanceDef{} -> [inst]
        other -> concatMap collectInstances (exprChildren other)
    
    collectInstance :: InstanceEnv -> Expr -> InstanceEnv
    collectInstance env (ExprInstanceDef className dataTypeName _ _) =
        let instanceType = TConstructor (TypeConstructor dataTypeName KindStar)
        in Map.insert (className, instanceType) True env
    collectInstance env _ = env
