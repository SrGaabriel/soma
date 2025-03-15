{-# LANGUAGE MultiParamTypeClasses #-}
module Analysis.Inference where

import Data.Map as Map
import Control.Monad.State
import Control.Monad.Except
import Parsing.Tree (Expression(..))

import Parsing.Type (Type(..), TypeVar(..))
import Analysis.Errors (AnalysisError(..))
import Control.Monad (foldM)

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

type Substitution = Map.Map TypeVar Type

class Substitutable a where
    apply :: Substitution -> a -> a

instance Substitutable Type where
    apply subst (TupleType ts) = TupleType (Prelude.map (apply subst) ts)
    apply _ x = x

type TypeMap = Map.Map Expression Type

data InferState = InferState
  { inferNextVar :: Int
  , inferTypeMap :: TypeMap
  } deriving (Show)


fresh :: InferM Type
fresh = do
    s <- get
    let i = inferNextVar s
    put s { inferNextVar = i + 1 }
    pure $ VarType (TypeVar "t" i)

unify :: Expression -> Type -> Expression -> Type -> InferM Substitution
unify expr (TupleType ts1) expr2 (TupleType ts2)
  | length ts1 == length ts2 = do
      s <- (foldM (\s (t1, t2) -> do
            s1 <- unify expr (apply s t1) expr2 (apply s t2)
            pure $ composeS s1 s
         ) Map.empty (ts1 `zip` ts2))
      pure s
  | otherwise = throwError $ TupleLengthMismatch expr expr2
unify expr (FunctionType args1 ret1) expr2 (FunctionType args2 ret2)
  | length args1 == length args2 = do
      s1 <- (foldM (\s (t1, t2) -> do
            s1 <- unify expr (apply s t1) expr2 (apply s t2)
            pure $ composeS s1 s
         ) Map.empty (args1 `zip` args2))
      s2 <- unify expr (apply s1 ret1) expr2 (apply s1 ret2)
      pure (composeS s2 s1)
  | otherwise = throwError $ FunctionArgumentLengthMismatch expr expr
unify expr (VarType v) _ t = bind expr v t
unify expr t _ (VarType v) = bind expr v t
unify expr (UnresolvedStructType n1) expr2 (UnresolvedStructType n2)
  | n1 == n2 = pure Map.empty
  | otherwise = throwError $ DifferentStructures expr expr2
unify _ _ _ _ = pure Map.empty

bind :: Expression -> TypeVar -> Type -> InferM Substitution
bind expr v t 
    | t == VarType v = pure Map.empty
    | occurs v t = throwError $ CircularTypeDependency expr
    | otherwise = pure $ Map.singleton v t

occurs :: TypeVar -> Type -> Bool
occurs v (VarType v') = v == v'
occurs v (TupleType ts) = any (occurs v) ts
occurs v (FunctionType args ret) = any (occurs v) args || occurs v ret
occurs v (ForAll vars t) = v `notElem` vars && occurs v t
occurs _ _ = False

composeS :: Substitution -> Substitution -> Substitution
composeS s1 s2 = Map.map (apply s1) s2 `Map.union` s1

evalInferM :: InferM a -> InferState -> IO (Either AnalysisError a)
evalInferM m st = pure $ evalState (runExceptT (runInfer m)) st

cleanEvalInferM :: InferM a -> IO (Either AnalysisError a)
cleanEvalInferM m = evalInferM m (InferState 0 Map.empty)

runInferM :: InferM a -> InferState -> IO (Either AnalysisError a, InferState)
runInferM m st = pure $ runState (runExceptT (runInfer m)) st

cleanRunInferM :: InferM a -> IO (Either AnalysisError a, InferState)
cleanRunInferM m = runInferM m (InferState 0 Map.empty)