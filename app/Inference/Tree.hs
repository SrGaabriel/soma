module Inference.Tree where

import Inference.Assembler (inferType)
import Inference.Core (InstanceEnv, TypeEnv, TypeMap)
import Inference.Errors (InferenceError)
import Inference.Resolver (runResolverWithEnv)
import Syntax.Tree (Expr (..))

analyzeTree :: TypeEnv -> InstanceEnv -> Expr -> Either [InferenceError] TypeMap
analyzeTree tEnv iEnv root = do
    case inferType tEnv iEnv root of
        Left err -> Left err
        Right (_rootType, typeMap) -> Right typeMap

analyzeTreeT :: TypeEnv -> Expr -> IO (Either [InferenceError] TypeMap)
analyzeTreeT tEnv root = do
    resolverResult <- runResolverWithEnv tEnv root
    case resolverResult of
        Left err -> pure $ Left [err]
        Right (_resolvedExpr, finalTypeEnv, instanceEnv) -> 
            pure $ analyzeTree finalTypeEnv instanceEnv root
