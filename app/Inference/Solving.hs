{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Inference.Solving where

import Control.Monad (foldM)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Debug.Trace as Debug
import Inference.Core (ClassEnv, TypeEnv)
import Inference.Errors (InferenceError (..))
import Inference.Gen (TypeConstraint (..))
import Syntax.Tree (Expr (..))
import Typing.Types (Constraint (..), QualifiedType (..), TyVar (..), Type (..))

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
    ftv (TVar tv) = Set.singleton tv
    ftv (TConstructor _) = Set.empty
    ftv (TApp t1 t2) = ftv t1 `Set.union` ftv t2
    ftv (TArrow t1 t2) = ftv t1 `Set.union` ftv t2
    ftv (TUnresolved name) = error $ "Unresolved type found during free type variable computation. TUnresolved should not reach inference: " ++ name

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
    apply s (Forall tvs cs t) = Forall tvs (apply s cs) (apply s s't)
      where
        s' = foldr Map.delete s tvs
        s't = apply s' t
    ftv (Forall tvs cs t) = (ftv cs `Set.union` ftv t) `Set.difference` (Set.fromList tvs)

instance (Substitutable a) => Substitutable [a] where
    apply s = Prelude.map (apply s)
    ftv = Set.unions . Prelude.map ftv

instance Substitutable TypeEnv where
    apply s = Map.map (apply s)
    ftv = ftv . Map.elems

composeSubst :: Subst -> Subst -> Subst
s1 `composeSubst` s2 = Map.map (apply s1) s2 `Map.union` s1

unifyPure :: Expr -> Type -> Type -> Either InferenceError Subst
unifyPure _ t1 t2 | t1 == t2 = Right Map.empty
unifyPure expr (TVar tv) t = bind expr tv t
unifyPure expr t (TVar tv) = bind expr tv t
unifyPure expr (TArrow l1 r1) (TArrow l2 r2) = do
    s1 <- unifyPure expr l1 l2
    s2 <- unifyPure expr (apply s1 r1) (apply s1 r2)
    return (composeSubst s2 s1)
unifyPure expr (TApp f1 a1) (TApp f2 a2) = do
    s1 <- unifyPure expr f1 f2
    s2 <- unifyPure expr (apply s1 a1) (apply s1 a2)
    return (composeSubst s2 s1)
unifyPure expr t1 t2 = Left $ TypeMismatch expr t1 t2

bind :: Expr -> TyVar -> Type -> Either InferenceError Subst
bind expr tv t
    | t == TVar tv = return Map.empty
    | tv `Set.member` ftv t = Left $ CircularTypeDependency expr
    | otherwise = return $ Map.singleton tv t

solveTypeConstraints :: [TypeConstraint] -> Either InferenceError Subst
solveTypeConstraints constraints = foldM solveOne Map.empty constraints
  where
    solveOne :: Subst -> TypeConstraint -> Either InferenceError Subst
    solveOne currentSubst (TypeConstraint expr expected actual) = do
        let expected' = apply currentSubst expected
        let actual' = apply currentSubst actual
        newSubst <- unifyPure expr expected' actual'
        return (composeSubst newSubst currentSubst)

solveClassConstraints :: ClassEnv -> [Constraint] -> Either InferenceError [Constraint]
solveClassConstraints _classEnv constraints =
    Debug.trace ("Now solving " ++ show constraints) $ Right constraints
