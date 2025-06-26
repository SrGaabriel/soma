module Inference.Assembler where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Inference.Core (ClassEnv, TypeEnv, TypeMap)
import Inference.Errors (InferenceError)
import Inference.Gen (ConstraintSet (csClassConstraints, csTypeConstraints), GenState (gsTypeMap), applyConstraintSubst, applyTySubst, generateConstraints, runGenM)
import Inference.Solving (Substitutable (ftv), solveClassConstraints, solveTypeConstraints)
import Syntax.Tree (Expr)
import Typing.Types (Constraint, QualifiedType (Forall), TyVar, Type)

inferType :: TypeEnv -> ClassEnv -> Expr -> Either [InferenceError] (Maybe QualifiedType, TypeMap)
inferType env classEnv expr =
    let ((maybeType, constraintSet), genState, genErrors) = runGenM env (generateConstraints expr)
        typeSubstResult = solveTypeConstraints (csTypeConstraints constraintSet)
    in case (genErrors, typeSubstResult) of
        ([], Right typeSubst) -> do
            let classConstraints = map (applyConstraintSubst typeSubst) (csClassConstraints constraintSet)
            solvedClassConstraints <- solveClassConstraints classEnv classConstraints
            let substTypeMap = Map.map (applyTySubst typeSubst) (gsTypeMap genState)
                qualifiedTypeMap = Map.map (generalize (ftv env) solvedClassConstraints) substTypeMap
            let result = fmap (generalize (ftv env) solvedClassConstraints . applyTySubst typeSubst) maybeType
            return (result, qualifiedTypeMap)
        (_, Left typeErrors) -> Left (genErrors ++ typeErrors)
        (errs, Right _) -> Left errs

generalize :: Set.Set TyVar -> [Constraint] -> Type -> QualifiedType
generalize envVars constraints t =
    let freeInType = ftv t `Set.difference` envVars
        quantifiedVars = Set.toList freeInType
    in Forall quantifiedVars constraints t
