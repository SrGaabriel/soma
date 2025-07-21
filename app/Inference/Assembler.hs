module Inference.Assembler where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Inference.Core (InstanceEnv, TypeEnv, TypeMap)
import Inference.Errors (InferenceError (..))
import Inference.Gen (ClassConstraintWithSource (..), ConstraintSet (csClassConstraints, csDeclaredConstraints, csTypeConstraints), GenState (gsTypeMap), generateConstraints, runGenM)
import Inference.Solving (checkConstraintEntailment, solveTypeConstraints)
import Inference.Substitution (Substitutable (apply, ftv))
import Syntax.Tree (Expr)
import Typing.Types (Constraint (..), QualifiedType (Forall), TyVar, Type (..))
import Inference.Resolver (runResolverWithEnv)

inferType :: String -> TypeEnv -> InstanceEnv -> Expr -> Either [InferenceError] (Maybe QualifiedType, TypeMap)
inferType currentModule env instanceEnv expr =
    let ((maybeType, constraintSet), genState, genErrors) = runGenM currentModule env (generateConstraints expr)
        typeSubstResult = solveTypeConstraints (csTypeConstraints constraintSet)
    in case (genErrors, typeSubstResult) of
        ([], Right typeSubst) -> do
            let classConstraintsWithSource = csClassConstraints constraintSet
            let classConstraints = map (apply typeSubst . ccsConstraint) classConstraintsWithSource
            let declaredConstraints = map (apply typeSubst) (csDeclaredConstraints constraintSet)

            case checkConstraintEntailment instanceEnv declaredConstraints classConstraintsWithSource typeSubst of
                Left constraintErrors -> Left constraintErrors
                Right () -> do
                    let substTypeMap = Map.map (apply typeSubst) (gsTypeMap genState)
                        qualifiedTypeMap = Map.map (generalize (ftv env) classConstraints) substTypeMap
                    let result = fmap (generalize (ftv env) classConstraints . apply typeSubst) maybeType
                    return (result, qualifiedTypeMap)
        (_, Left typeErrors) -> Left (genErrors ++ typeErrors)
        (errs, Right _) -> Left errs

generalize :: Set.Set TyVar -> [Constraint] -> Type -> QualifiedType
generalize envVars constraints t =
    let freeInType = ftv t `Set.difference` envVars
        quantifiedVars = Set.toList freeInType
        relevant = filter (\c -> not (Set.null (ftv c `Set.intersection` freeInType))) constraints
        uniqueConstraints = Set.toList (Set.fromList relevant)
    in Forall quantifiedVars uniqueConstraints t

inferTree :: String -> TypeEnv -> InstanceEnv -> Expr -> Either [InferenceError] TypeMap
inferTree currentModule tEnv iEnv root = do
    case inferType currentModule tEnv iEnv root of
        Left err -> Left err
        Right (_rootType, typeMap) -> Right typeMap

inferTreeT :: String -> TypeEnv -> Expr -> IO (Either [InferenceError] TypeMap)
inferTreeT currentModule tEnv root = do
    resolverResult <- runResolverWithEnv currentModule tEnv root
    case resolverResult of
        Left err -> pure $ Left [err]
        Right (_resolvedExpr, finalTypeEnv, instanceEnv) ->
            pure $ inferTree currentModule finalTypeEnv instanceEnv root