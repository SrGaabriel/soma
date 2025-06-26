module Inference.Tree where

import qualified Data.Map as Map
import Inference.Assembler (inferType)
import Inference.Core (ClassEnv, TypeEnv, TypeMap)
import Inference.Errors (InferenceError)
import Syntax.Tree (Expr)

analyzeTree :: TypeEnv -> ClassEnv -> Expr -> Either [InferenceError] TypeMap
analyzeTree tEnv cEnv root = do
    case inferType tEnv cEnv root of
        Left err -> Left err
        Right (_rootType, typeMap) -> Right typeMap

analyzeTreeT :: TypeEnv -> Expr -> Either [InferenceError] TypeMap
analyzeTreeT tEnv root = do
    let cEnv = Map.empty
    analyzeTree tEnv cEnv root
