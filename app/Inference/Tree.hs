module Inference.Tree where

import qualified Data.Map as Map
import Inference.Assembler (inferType)
import Inference.Core (ClassEnv, TypeEnv, TypeMap)
import Inference.Errors (InferenceError)
import Syntax.Tree (Expr, exprChildren)

analyzeTree :: TypeEnv -> ClassEnv -> Expr -> Either InferenceError TypeMap
analyzeTree tEnv cEnv root = go root
  where
    go expr = do
        inferredType <- inferType tEnv cEnv expr
        childMaps <- mapM go (exprChildren expr)
        case inferredType of
            Nothing -> Right $ Map.unions childMaps
            Just inferredType' -> do
                let current = Map.singleton expr inferredType'
                Right $ Map.unions (current : childMaps)

analyzeTreeT :: TypeEnv -> Expr -> Either InferenceError TypeMap
analyzeTreeT tEnv root = do
    let cEnv = Map.empty
    analyzeTree tEnv cEnv root