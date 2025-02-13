{-# LANGUAGE MultiParamTypeClasses #-}
module Analysis.Tree where

import Data.Map as Map
import Data.Set as Set
import Control.Monad.State
import Control.Monad.Except
import Parsing.Tree (Expression(..))

import Parsing.Type
import Analysis.Errors (AnalysisError(..))

data TypeScheme
    = STypeLiteral Type
    | STypeVar Int
    | STypeLambda TypeScheme TypeScheme
    deriving (Eq, Show)

newtype InferM a = InferM {
    runInfer :: ExceptT AnalysisError (State InferState) a
}

instance Functor InferM where
    fmap f m = InferM $ fmap f (runInfer m)

instance Applicative InferM where
    pure x = InferM $ pure x
    f <*> x = InferM $ runInfer f <*> runInfer x

instance Monad InferM where
    m >>= k = InferM $ runInfer m >>= runInfer . k

instance MonadState InferState InferM where
    get = InferM get
    put = InferM . put

instance MonadError AnalysisError InferM where
    throwError = InferM . throwError
    catchError m h = InferM $ catchError (runInfer m) (runInfer . h)

type Substitution = Map.Map Int TypeScheme

class Substitutable a where
    free :: a -> Set.Set Int
    apply :: Substitution -> a -> a

instance Substitutable TypeScheme where
    free (STypeLiteral _) = Set.empty
    free (STypeVar v) = Set.singleton v
    free (STypeLambda t1 t2) = free t1 `Set.union` free t2

    apply _ t@(STypeLiteral _) = t
    apply s (STypeVar v) = Map.findWithDefault (STypeVar v) v s
    apply s (STypeLambda t1 t2) = STypeLambda (apply s t1) (apply s t2)

data InferState = InferState
  { inferNextVar :: Int
  , inferTypeMap :: Map.Map Expression Type
  }

fresh :: InferM TypeScheme
fresh = do
    st <- get
    put $ st { inferNextVar = inferNextVar st + 1 }
    return $ STypeVar $ inferNextVar st

unify :: Expression -> TypeScheme -> TypeScheme -> InferM Substitution
unify expr (STypeVar v) t = bind expr v t
unify expr t (STypeVar v) = bind expr v t
unify expr (STypeLiteral t1) (STypeLiteral t2)
    | t1 == t2 = return Map.empty
    | otherwise = throwError $ UnificationError $ expr
unify expr (STypeLambda t1 t2) (STypeLambda t3 t4) = do
    s1 <- unify expr t1 t3
    s2 <- unify expr (apply s1 t2) (apply s1 t4)
    return $ s2 `Map.union` s1
unify expr _ _ = throwError $ UnificationError $ expr

bind :: Expression -> Int -> TypeScheme -> InferM Substitution
bind expr v t 
    | t == STypeVar v = return Map.empty
    | v `Set.member` free t = throwError $ UnificationError expr
    | otherwise = return $ Map.singleton v t

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = Map.map (apply s1) s2 `Map.union` s1