module Inference.Assembler where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Inference.Core (ClassEnv, TypeEnv, TypeMap)
import Inference.Errors (InferenceError)
import Inference.Gen (ConstraintSet (csClassConstraints, csTypeConstraints), GenState (gsTypeMap), applyConstraintSubst, applyTySubst, generateConstraints, runGenM)
import Inference.Solving (Substitutable (ftv), solveClassConstraints, solveTypeConstraints)
import Syntax.Tree (Expr)
import Typing.Types (Constraint, QualifiedType (Forall), TyVar, Type)

inferType :: TypeEnv -> ClassEnv -> Expr -> Either InferenceError (Maybe QualifiedType, TypeMap)
inferType env classEnv expr = do
    let ((maybeType, constraintSet), genState) = runGenM env (generateConstraints expr)

    typeSubst <- solveTypeConstraints (csTypeConstraints constraintSet)

    let classConstraints = map (applyConstraintSubst typeSubst) (csClassConstraints constraintSet)
    solvedClassConstraints <- solveClassConstraints classEnv classConstraints

    let substitutedTypeMap = Map.map (applyTySubst typeSubst) (gsTypeMap genState)

    let qualifiedTypeMap = Map.map (generalize (ftv env) solvedClassConstraints) substitutedTypeMap

    case maybeType of
        Nothing ->
            return (Nothing, qualifiedTypeMap)
        Just exprType -> do
            let finalType = applyTySubst typeSubst exprType
            let rootQualifiedType = generalize (ftv env) solvedClassConstraints finalType
            return (Just rootQualifiedType, qualifiedTypeMap)

generalize :: Set.Set TyVar -> [Constraint] -> Type -> QualifiedType
generalize envVars constraints t =
    let freeInType = ftv t `Set.difference` envVars
        quantifiedVars = Set.toList freeInType
    in Forall quantifiedVars constraints t
