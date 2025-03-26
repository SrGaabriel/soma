{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TupleSections #-}
module Analysis.Inference where

import Data.Map as Map
import Control.Monad.State
import Control.Monad.Except
import Parsing.Tree (Expression(..))

import Parsing.Type (Type(..), TypeVar(..), StructVariant (variantFields))
import Analysis.Errors (AnalysisError(..))
import Control.Monad (foldM)
import Data.List (nub)

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
    apply subst t = case t of
        UnresolvedVarType v -> Map.findWithDefault t v subst
        TupleType ts -> TupleType (Prelude.map (apply subst) ts)
        FunctionType args ret -> FunctionType (Prelude.map (apply subst) args) (apply subst ret)
        StructType n variants mgs -> 
            StructType n 
                       (Prelude.map (\v -> v { variantFields = Map.map (apply subst) (variantFields v) }) variants)
                       (fmap (Prelude.map (apply subst)) mgs)
        UnresolvedStructType n mgs -> 
            UnresolvedStructType n (fmap (Prelude.map (apply subst)) mgs)
        _ -> t

type TypeMap = Map.Map Expression Type

type TypeEnv = Map.Map String Type

data InferState = InferState
    { inferNextVar :: Int
    , inferTypeMap :: TypeMap
    , globalEnv :: TypeEnv
    , structTypes :: Map.Map String Type
    } deriving (Show)

fresh :: InferM Type
fresh = do
    s <- get
    let i = inferNextVar s
    put s { inferNextVar = i + 1 }
    pure $ UnresolvedVarType (TypeVar "t" i)

unify :: Expression -> Type -> Type -> InferM Substitution
unify expr (StructType n1 vars1 mgs1) (StructType n2 vars2 mgs2)
    | n1 == n2 = case (mgs1, mgs2) of
        (Nothing, Nothing) -> pure Map.empty
        (Just gs1, Just gs2) | length gs1 == length gs2 -> 
            foldM (\s (g1, g2) -> do
                s' <- unify expr (apply s g1) (apply s g2)
                pure (composeS s' s)
            ) Map.empty (zip gs1 gs2)
        _ -> throwError $ TypeMismatch expr (StructType n1 vars1 mgs1) (StructType n2 vars2 mgs2)
    | otherwise = throwError $ TypeMismatch expr (StructType n1 vars1 mgs1) (StructType n2 vars2 mgs2)
unify expr (UnresolvedVarType v) t = bind expr v t
unify expr t (UnresolvedVarType v) = bind expr v t

unify expr u@(UnresolvedStructType _ _) t = do
    replaced <- replaceStruct expr u
    unify expr replaced t
unify expr t u@(UnresolvedStructType _ _) =
    unify expr u t

unify expr (FunctionType args1 ret1) (FunctionType args2 ret2)
    | length args1 == length args2 = do
        s1 <- foldM (\s (a1, a2) -> do
            s' <- unify expr (apply s a1) (apply s a2)
            pure (composeS s' s)
            ) Map.empty (zip args1 args2)
        s2 <- unify expr (apply s1 ret1) (apply s1 ret2)
        pure (composeS s2 s1)
    | otherwise = throwError $ TypeMismatch expr (FunctionType args1 ret1) (FunctionType args2 ret2)
unify expr t1 t2
    | t1 == t2 = pure Map.empty
    | otherwise = throwError $ TypeMismatch expr t1 t2

replaceStruct :: Expression -> Type -> InferM Type
replaceStruct expr (UnresolvedStructType name generics) = do
    s <- get
    case Map.lookup name (structTypes s) of
        Just (StructType stName stVariants _) -> pure $ StructType stName stVariants generics
        _ -> throwError $ UnknownStruct expr name
replaceStruct _ t = pure t

bind :: Expression -> TypeVar -> Type -> InferM Substitution
bind expr v t 
    | t == UnresolvedVarType v = pure Map.empty
    | occurs v t = throwError $ CircularTypeDependency expr
    | otherwise = pure $ Map.singleton v t

occurs :: TypeVar -> Type -> Bool
occurs v (UnresolvedVarType v') = v == v'
occurs v (TupleType ts) = any (occurs v) ts
occurs v (FunctionType args ret) = any (occurs v) args || occurs v ret
occurs _ _ = False

collectGenerics :: Type -> [String]
collectGenerics (GenericType g) = [g]
collectGenerics (TupleType ts) = concatMap collectGenerics ts
collectGenerics (FunctionType args ret) = concatMap collectGenerics args ++ collectGenerics ret
collectGenerics (StructType _ variants mgs) = 
    concatMap (collectGenerics . snd) (concatMap Map.toList (Prelude.map variantFields variants)) ++ 
    maybe [] (concatMap collectGenerics) mgs
collectGenerics (UnresolvedStructType _ mgs) = maybe [] (concatMap collectGenerics) mgs
collectGenerics _ = []

replaceGenerics :: Map.Map String Type -> Type -> Type
replaceGenerics subst (GenericType g) = Map.findWithDefault (GenericType g) g subst
replaceGenerics subst (TupleType ts) = TupleType (Prelude.map (replaceGenerics subst) ts)
replaceGenerics subst (FunctionType args ret) = 
    FunctionType (Prelude.map (replaceGenerics subst) args) (replaceGenerics subst ret)
replaceGenerics subst (StructType n variants mgs) = 
    StructType n 
               (Prelude.map (\v -> v { variantFields = Map.map (replaceGenerics subst) (variantFields v) }) variants)
               (fmap (Prelude.map (replaceGenerics subst)) mgs)
replaceGenerics subst (UnresolvedStructType n mgs) = 
    UnresolvedStructType n (fmap (Prelude.map (replaceGenerics subst)) mgs)
replaceGenerics _ t = t

instantiate :: Type -> InferM Type
instantiate ty = do
    let generics = nub $ collectGenerics ty
    subst <- Map.fromList <$> mapM (\g -> (g,) <$> fresh) generics
    pure $ replaceGenerics subst ty

composeS :: Substitution -> Substitution -> Substitution
composeS s1 s2 = Map.map (apply s1) s2 `Map.union` s1

evalInferM :: InferM a -> InferState -> IO (Either AnalysisError a)
evalInferM m st = pure $ evalState (runExceptT (runInfer m)) st

cleanEvalInferM :: InferM a -> IO (Either AnalysisError a)
cleanEvalInferM m = evalInferM m (InferState 0 Map.empty Map.empty Map.empty)

runInferM :: InferM a -> InferState -> IO (Either AnalysisError a, InferState)
runInferM m st = pure $ runState (runExceptT (runInfer m)) st

cleanRunInferM :: InferM a -> IO (Either AnalysisError a, InferState)
cleanRunInferM m = runInferM m (InferState 0 Map.empty Map.empty Map.empty)