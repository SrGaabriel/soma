{-# LANGUAGE FlexibleInstances #-}

module Inference.Solving where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Inference.Core (ClassEnv, TypeEnv, UnificationPurpose(..))
import Inference.Errors (InferenceError (..), generateErrorForPurpose)
import Inference.Gen (TypeConstraint (..))
import Syntax.Tree (Expr (..))
import Typing.Types (Constraint (..), QualifiedType (..), TyVar (..), Type (..))
import Utils.Lists (foldMWithErrors)

type Subst = Map.Map TyVar Type

class Substitutable a where
    apply :: Subst -> a -> a
    ftv :: a -> Set.Set TyVar

instance Substitutable Type where
    apply s (TVar tv) = case Map.lookup tv s of
        Nothing -> TVar tv
        Just t -> t
    apply _ (TConstructor tc) = TConstructor tc
    apply s (TApp t1 t2) = TApp (apply s t1) (apply s t2)
    apply s (TArrow t1 t2) = TArrow (apply s t1) (apply s t2)
    apply _ (TUnresolved name) = error $ "Cannot apply substitution to an unresolved type. TUnresolved should not reach inference: " ++ name
    apply _ (TSkolem sv) = TSkolem sv
    ftv (TVar tv) = Set.singleton tv
    ftv (TConstructor _) = Set.empty
    ftv (TApp t1 t2) = ftv t1 `Set.union` ftv t2
    ftv (TArrow t1 t2) = ftv t1 `Set.union` ftv t2
    ftv (TUnresolved name) = error $ "Unresolved type found during free type variable computation. TUnresolved should not reach inference: " ++ name
    ftv (TSkolem _) = Set.empty

instance Substitutable TyVar where
    apply s tv = case Map.lookup tv s of
        Nothing -> tv
        Just t -> case t of
            TVar tv' -> tv'
            _ -> error "Attempted to apply substitution that maps TyVar to non-TVar type during TyVar substitution (should return a TyVar)"
    ftv = Set.singleton

instance Substitutable Constraint where
    apply s (Constraint n ts) = Constraint n (map (apply s) ts)
    ftv (Constraint _ ts) = Set.unions $ map ftv ts

instance Substitutable QualifiedType where
    apply s (Forall tvs cs t) =
        let s' = foldr Map.delete s tvs
        in Forall tvs (apply s' cs) (apply s' t)
    ftv (Forall tvs cs t) = (ftv cs `Set.union` ftv t) `Set.difference` (Set.fromList tvs)

instance (Substitutable a) => Substitutable [a] where
    apply s = Prelude.map (apply s)
    ftv = Set.unions . Prelude.map ftv

instance Substitutable TypeEnv where
    apply s = Map.map (apply s)
    ftv = ftv . Map.elems

composeSubst :: Subst -> Subst -> Subst
s1 `composeSubst` s2 = Map.map (apply s1) s2 `Map.union` s1

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
solveClassConstraints _classEnv = Right
