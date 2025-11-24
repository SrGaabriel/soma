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

inferType :: String -> String -> TypeEnv -> InstanceEnv -> Expr -> ([InferenceError], (Maybe QualifiedType, TypeMap))
inferType currentPackage currentModule env instanceEnv expr =
    let ((maybeType, constraintSet), genState, genErrors) = runGenM currentPackage currentModule env (generateConstraints expr)
        typeSubstResult = solveTypeConstraints (csTypeConstraints constraintSet)
    in case typeSubstResult of
        Right typeSubst -> do
            let classConstraintsWithSource = csClassConstraints constraintSet
            let classConstraints = map (apply typeSubst . ccsConstraint) classConstraintsWithSource
            let declaredConstraints = map (apply typeSubst) (csDeclaredConstraints constraintSet)
            case checkConstraintEntailment instanceEnv declaredConstraints classConstraintsWithSource typeSubst of
                Left constraintErrors ->
                    let allErrors = genErrors ++ constraintErrors
                    in (allErrors, (Nothing, Map.empty))
                Right () ->
                    let substTypeMap = Map.map (apply typeSubst) (gsTypeMap genState)
                        qualifiedTypeMap = Map.map (generalize (ftv env) classConstraints) substTypeMap
                        result = fmap (generalize (ftv env) classConstraints . apply typeSubst) maybeType
                    in (genErrors, (result, qualifiedTypeMap))
        Left typeErrors ->
            (genErrors ++ typeErrors, (Nothing, Map.empty))

generalize :: Set.Set TyVar -> [Constraint] -> Type -> QualifiedType
generalize envVars constraints t =
    let freeInType = ftv t `Set.difference` envVars
        quantifiedVars = Set.toList freeInType
        relevant =
            filter
                ( \c ->
                    let constraintFreeVars = ftv c `Set.intersection` freeInType
                    in not (Set.null constraintFreeVars) || Set.null (ftv c `Set.difference` envVars)
                )
                constraints
        uniqueConstraints = Set.toList (Set.fromList relevant)
    in Forall quantifiedVars uniqueConstraints t

inferTree :: String -> String -> TypeEnv -> InstanceEnv -> Expr -> ([InferenceError], TypeMap)
inferTree currentPackage currentModule tEnv iEnv root =
    let (errors, (_rootType, tyMap)) = inferType currentPackage currentModule tEnv iEnv root
    in (errors, tyMap)
