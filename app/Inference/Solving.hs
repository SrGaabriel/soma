{-# LANGUAGE LambdaCase, FlexibleInstances #-}

module Inference.Solving where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Inference.Core (ClassEnv, InstanceEnv, UnificationPurpose (..))
import Inference.Errors (InferenceError (..), generateErrorForPurpose)
import Inference.Gen (TypeConstraint (..), ClassConstraintWithSource (..))
import Inference.Substitution (Subst, Substitutable(apply, ftv), composeSubst)
import Syntax.Tree (Expr (..))
import Typing.Types (Constraint (..), TyVar (..), Type (..))
import Utils.Lists (foldMWithErrors)

unifyPure :: Expr -> UnificationPurpose -> Type -> Type -> Either [InferenceError] Subst
unifyPure _ _ t1 t2 | t1 == t2 = Right Map.empty
unifyPure expr _ (TVar tv) t = bind expr tv t
unifyPure expr _ t (TVar tv) = bind expr tv t
unifyPure expr p (TArrow l1 r1) (TArrow l2 r2) = do
    s1 <- unifyPure expr p l1 l2
    s2 <- unifyPure expr p (apply s1 r1) (apply s1 r2)
    return (composeSubst s2 s1)
unifyPure expr p (TApp f1 a1) (TApp f2 a2) = do
    s1 <- unifyPure expr p f1 f2
    s2 <- unifyPure expr p (apply s1 a1) (apply s1 a2)
    return (composeSubst s2 s1)
unifyPure expr p t1 t2 = Left [generateErrorForPurpose p expr t1 t2]

bind :: Expr -> TyVar -> Type -> Either [InferenceError] Subst
bind expr tv t
    | t == TVar tv = return Map.empty
    | tv `Set.member` ftv t = Left [CircularTypeDependency expr]
    | otherwise = return $ Map.singleton tv t

solveTypeConstraints :: [TypeConstraint] -> Either [InferenceError] Subst
solveTypeConstraints = foldMWithErrors solveOne Map.empty
  where
    solveOne :: Subst -> TypeConstraint -> Either [InferenceError] Subst
    solveOne currentSubst (TypeConstraint expr expected actual purpose) = do
        let expected' = apply currentSubst expected
        let actual' = apply currentSubst actual
        newSubst <- unifyPure expr purpose expected' actual'
        return (composeSubst newSubst currentSubst)

solveClassConstraints :: ClassEnv -> [Constraint] -> Either [InferenceError] [Constraint]
solveClassConstraints _classEnv constraints = do
    Right constraints

checkConstraintEntailment :: InstanceEnv -> [Constraint] -> [ClassConstraintWithSource] -> Subst -> Either [InferenceError] ()
checkConstraintEntailment instanceEnv declaredConstraints classConstraintsWithSource typeSubst = do
    let inferredConstraints = map (\ccs -> (apply typeSubst (ccsConstraint ccs), ccsSourceExpr ccs)) classConstraintsWithSource
    let unsatisfiedConstraints = filter (not . isConstraintSatisfied) inferredConstraints
    case unsatisfiedConstraints of
        [] -> Right ()
        ((constraint, sourceExpr):_) -> Left [MissingClassConstraint sourceExpr constraint]
  where
    isConstraintSatisfied (constraint, _) = 
        isEntailedByInstanceEnv instanceEnv constraint || isEntailedBy declaredConstraints constraint

isEntailedByInstanceEnv :: InstanceEnv -> Constraint -> Bool
isEntailedByInstanceEnv instanceEnv (Constraint className [typ]) =
    case className of
        "Eq" -> Map.lookup ("Eq", typ) instanceEnv == Just True
        _ -> False
isEntailedByInstanceEnv _ _ = False

hasEqualityFromConstraints :: [Constraint] -> Type -> Bool
hasEqualityFromConstraints constraints targetType =
    any (\case
        Constraint cname [ctype] -> 
            cname == "Eq" && (ctype == targetType || isTypeVarMatch ctype targetType)
        _ -> False) constraints

isTypeVarMatch :: Type -> Type -> Bool
isTypeVarMatch (TVar _) _ = True
isTypeVarMatch (TSkolem _) _ = True
isTypeVarMatch _ _ = False

isEntailedBy :: [Constraint] -> Constraint -> Bool
isEntailedBy declaredCs (Constraint name typs) =
    any (\(Constraint declName declTyps) -> 
        declName == name && length declTyps == length typs && 
        and (zipWith (==) declTyps typs)) declaredCs