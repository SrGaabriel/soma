module Inference.Assembler where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Inference.Core (ClassEnv, InstanceEnv, TypeEnv, TypeMap)
import Inference.Errors (InferenceError (..))
import Inference.Gen (ConstraintSet (csClassConstraints, csTypeConstraints, csDeclaredConstraints), GenState (gsTypeMap), ClassConstraintWithSource (..), generateConstraints, runGenM)
import Inference.Substitution (Substitutable (ftv, apply))
import Inference.Solving (checkConstraintEntailment, solveClassConstraints, solveTypeConstraints)
import Syntax.Tree (Expr)
import Typing.Types (Constraint (..), QualifiedType (Forall), TyVar, Type (..))

inferType :: TypeEnv -> ClassEnv -> InstanceEnv -> Expr -> Either [InferenceError] (Maybe QualifiedType, TypeMap)
inferType env classEnv instanceEnv expr =
    let ((maybeType, constraintSet), genState, genErrors) = runGenM env (generateConstraints expr)
        typeSubstResult = solveTypeConstraints (csTypeConstraints constraintSet)
    in case (genErrors, typeSubstResult) of
        ([], Right typeSubst) -> do
            let classConstraintsWithSource = csClassConstraints constraintSet
            let classConstraints = map (apply typeSubst . ccsConstraint) classConstraintsWithSource
            let declaredConstraints = map (apply typeSubst) (csDeclaredConstraints constraintSet)
            
            case checkConstraintEntailment instanceEnv declaredConstraints classConstraintsWithSource typeSubst of
                Left constraintErrors -> Left constraintErrors
                Right () -> do
                    solvedClassConstraints <- solveClassConstraints classEnv classConstraints
                    let substTypeMap = Map.map (apply typeSubst) (gsTypeMap genState)
                        qualifiedTypeMap = Map.map (generalize (ftv env) solvedClassConstraints) substTypeMap
                    let result = fmap (generalize (ftv env) solvedClassConstraints . apply typeSubst) maybeType
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
