{-# LANGUAGE FlexibleInstances #-}

module Inference.Substitution (Subst, Substitutable (apply, ftv), composeSubst) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Inference.Core (TypeEnv)
import Typing.Types (Constraint (..), QualifiedType (..), TyVar (..), Type (..), constraintType)

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
    apply _ t@(TUnresolved _) = t
    apply _ (TSkolem sv) = TSkolem sv
    ftv (TVar tv) = Set.singleton tv
    ftv (TConstructor _) = Set.empty
    ftv (TApp t1 t2) = ftv t1 `Set.union` ftv t2
    ftv (TArrow t1 t2) = ftv t1 `Set.union` ftv t2
    ftv (TUnresolved _) = Set.empty
    ftv (TSkolem _) = Set.empty

instance Substitutable TyVar where
    apply s tv = case Map.lookup tv s of
        Nothing -> tv
        Just t -> case t of
            TVar tv' -> tv'
            _ -> error "Attempted to apply substitution that maps TyVar to non-TVar type during TyVar substitution (should return a TyVar)"
    ftv = Set.singleton

instance Substitutable Constraint where
    apply s constraint =
        let t = constraintType constraint
            t' = apply s t
        in Constraint t'
    ftv constraint = ftv (constraintType constraint)

instance Substitutable QualifiedType where
    apply s (Forall tvs cs t) =
        let s' = foldr Map.delete s tvs
        in Forall tvs (apply s' cs) (apply s' t)
    ftv (Forall tvs cs t) = (ftv cs `Set.union` ftv t) `Set.difference` Set.fromList tvs

instance (Substitutable a) => Substitutable [a] where
    apply s = Prelude.map (apply s)
    ftv = Set.unions . Prelude.map ftv

instance Substitutable TypeEnv where
    apply s = Map.map (apply s)
    ftv = ftv . Map.elems

composeSubst :: Subst -> Subst -> Subst
s1 `composeSubst` s2 = Map.map (apply s1) s2 `Map.union` s1
