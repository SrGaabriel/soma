{-# LANGUAGE MultiParamTypeClasses #-}
module Analysis.Inference where

import Data.Map as Map
import Data.Set as Set
import Control.Monad.State
import Control.Monad.Except
import Parsing.Tree (Expression(..))

import Parsing.Type
import Analysis.Errors (AnalysisError(..))
import Control.Monad (foldM)

data TypeScheme
    = STypeLiteral Type
    | STypeVar Int
    | STypeLambda [TypeScheme] TypeScheme
    | SUntyped
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
    free (STypeLambda t1 t2) = Set.unions $ fmap free (t1 ++ [t2])
    free SUntyped = Set.empty

    apply _ t@(STypeLiteral _) = t
    apply s (STypeVar v) = Map.findWithDefault (STypeVar v) v s
    apply s (STypeLambda args ret) = STypeLambda (fmap (apply s) args) (apply s ret)
    apply _ SUntyped = SUntyped

data InferState = InferState
  { inferNextVar :: Int
  , inferTypeMap :: Map.Map Expression TypeScheme
  } deriving (Show)

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
unify expr (STypeLambda args1 ret1) (STypeLambda args2 ret2) = do
    if (length args1 /= length args2) then
        throwError $ DifferentArgumentLengths expr expr
    else do   
        argSubst <- foldM (\subst (a1, a2) -> do
            s <- unify expr (apply subst a1) (apply subst a2)
            return $ composeS s subst
            ) Map.empty (zip args1 args2)
            
        retSubst <- unify expr (apply argSubst ret1) (apply argSubst ret2)
        
        return $ composeS retSubst argSubst
unify expr _ _ = throwError $ UnificationError $ expr

bind :: Expression -> Int -> TypeScheme -> InferM Substitution
bind expr v t 
    | t == STypeVar v = return Map.empty
    | v `Set.member` free t = throwError $ UnificationError expr
    | otherwise = return $ Map.singleton v t

composeS :: Substitution -> Substitution -> Substitution
composeS s1 s2 = Map.map (apply s1) s2 `Map.union` s1

concretize :: TypeScheme -> Maybe Type
concretize (STypeLiteral t) = Just t
concretize (STypeLambda args ret) = do
    args' <- traverse concretize args
    ret' <- concretize ret
    return $ FunctionType args' ret'
concretize _ = Nothing

evalInferM :: InferM a -> InferState -> IO (Either AnalysisError a)
evalInferM m st = return $ evalState (runExceptT (runInfer m)) st

cleanEvalInferM :: InferM a -> IO (Either AnalysisError a)
cleanEvalInferM m = evalInferM m (InferState 0 Map.empty)

runInferM :: InferM a -> InferState -> IO (Either AnalysisError a, InferState)
runInferM m st = return $ runState (runExceptT (runInfer m)) st

cleanRunInferM :: InferM a -> IO (Either AnalysisError a, InferState)
cleanRunInferM m = runInferM m (InferState 0 Map.empty)