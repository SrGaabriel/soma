module Inference.Assembler where

import qualified Data.Set as Set
import Inference.Core (ClassEnv, TypeEnv)
import Inference.Gen (ConstraintSet (csClassConstraints, csTypeConstraints), applyConstraintSubst, applyTySubst, generateConstraints, runGenM)
import Inference.Solving (Substitutable (ftv), solveClassConstraints, solveTypeConstraints)
import Syntax.Tree (Expr)
import Typing.Types (Constraint, QualifiedType (Forall), TyVar, Type)
import Inference.Errors (InferenceError)

inferType :: TypeEnv -> ClassEnv -> Expr -> Either InferenceError (Maybe QualifiedType)
inferType env classEnv expr = do
    case runGenM (generateConstraints env expr) of
        (Nothing, _) -> pure Nothing
        (Just ((exprType, constraintSet)), _) -> do
            typeSubst <- solveTypeConstraints (csTypeConstraints constraintSet)

            let classConstraints = map (applyConstraintSubst typeSubst) (csClassConstraints constraintSet)
            solvedClassConstraints <- solveClassConstraints classEnv classConstraints

            let finalType = applyTySubst typeSubst exprType
            let generalizedType = generalize (ftv env) solvedClassConstraints finalType

            pure $ Just generalizedType

generalize :: Set.Set TyVar -> [Constraint] -> Type -> QualifiedType
generalize envVars constraints t =
    let freeInType = ftv t `Set.difference` envVars
        quantifiedVars = Set.toList freeInType
    in Forall quantifiedVars constraints t
