{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module Inference.Resolver where

import Control.Monad (when)
import Control.Monad.Except (ExceptT, MonadError (throwError), runExceptT)
import Control.Monad.State (MonadState (get, put), State, gets, runState)
import qualified Data.Map as Map
import Inference.Core (InstanceEnv, TypeEnv)
import Inference.Errors (InferenceError (..))
import Syntax.Tree (Expr (..), exprChildren)
import Typing.Currying (curryFunction)
import Typing.Types (Kind (..), QualifiedType (Forall), TyConstructor (TypeConstructor), TyVar (tvKind), Type (..), assignConstraints, sumQualifiedTypes)

newtype ResolverM a = ResolverM
    { runResolverM :: ExceptT InferenceError (State ResolverState) a
    }
    deriving (Functor, Applicative, Monad, MonadState ResolverState, MonadError InferenceError)

data ResolverState = ResolverState
    { globalBindings :: TypeEnv
    , instanceBindings :: InstanceEnv
    }

collectGlobals :: Expr -> ResolverM ()
collectGlobals (ExprRoot children) = do
    mapM_ collectGlobals children
collectGlobals (ExprBindingDef name bindType _ topLevel _) =
    when topLevel $ do
        addGlobalBinding name bindType
collectGlobals (ExprDataTypeDef name generics constraints constructors _) = do
    let kind = foldr (KindArrow . tvKind) KindStar generics
    let baseConstructor = TConstructor $ TypeConstructor name kind

    let structType =
            if null generics
                then baseConstructor
                else foldl TApp baseConstructor (map TVar generics)

    let constrainedStructType = Forall generics constraints structType
    addGlobalBinding name constrainedStructType

    mapM_
        ( \case
            ExprDataConstructor cName fields _ ->
                let fieldTypes = map snd fields
                    curried = curryFunction fieldTypes structType
                    qualified = assignConstraints constrainedStructType curried
                in addGlobalBinding cName qualified
            recv -> error $ "Expected StructConstructorExpr in struct definition but got " ++ show recv
        )
        constructors
collectGlobals _ = pure ()

collectInstances :: Expr -> ResolverM ()
collectInstances (ExprRoot children) = do
    mapM_ collectInstances children
collectInstances (ExprInstanceDef className dataTypeName _ _) = do
    let instanceType = TConstructor (TypeConstructor dataTypeName KindStar)
    addInstanceBinding className instanceType
collectInstances expr = do
    mapM_ collectInstances (exprChildren expr)

resolveTReference :: Expr -> ResolverM Expr
resolveTReference (ExprRoot children) = do
    children' <- mapM resolveTReference children
    pure $ ExprRoot children'
resolveTReference (ExprDataTypeDef name generics constraints constructors s) = do
    constructors' <- mapM resolveTReference constructors
    pure $ ExprDataTypeDef name generics constraints constructors' s
resolveTReference (ExprTypeClassDef name generics methods s) = do
    methods' <- mapM resolveTReference methods
    pure $ ExprTypeClassDef name generics methods' s
resolveTReference expr@(ExprTypeClassBinding name typ defaultV s) = do
    env <- getEnv
    realTyp <- replaceAllUnresolvedQualified expr env typ
    addGlobalBinding name realTyp
    pure $ ExprTypeClassBinding name realTyp defaultV s
resolveTReference (ExprInstanceDef className dataNam binds s) = do
    binds' <- mapM resolveTReference binds
    pure $ ExprInstanceDef className dataNam binds' s
resolveTReference expr@(ExprBindingDef a typ body topLevel c) = do
    env <- getEnv
    realTyp <- replaceAllUnresolvedQualified expr env typ
    body' <- resolveTReference body
    when topLevel $ do
        addGlobalBinding a realTyp

    pure $ ExprBindingDef a realTyp body' topLevel c
resolveTReference expr = pure expr

getEnv :: ResolverM TypeEnv
getEnv = gets globalBindings

getInstanceEnv :: ResolverM InstanceEnv
getInstanceEnv = gets instanceBindings

getReference :: Expr -> String -> ResolverM QualifiedType
getReference expr name = do
    s <- get
    case Map.lookup name (globalBindings s) of
        Just ty -> pure ty
        Nothing -> throwError $ UnknownTypeConstructor expr name

analyzeTree :: Expr -> ResolverM Expr
analyzeTree root = do
    collectGlobals root
    collectInstances root
    resolveTReference root

addGlobalBinding :: String -> QualifiedType -> ResolverM ()
addGlobalBinding name ty = do
    s <- get
    let globals = globalBindings s
    put s{globalBindings = Map.insert name ty globals}

addInstanceBinding :: String -> Type -> ResolverM ()
addInstanceBinding className instanceType = do
    s <- get
    let instances = instanceBindings s
    put s{instanceBindings = Map.insert (className, instanceType) True instances}

runResolver :: Expr -> IO (Either InferenceError (Expr, TypeEnv, InstanceEnv))
runResolver root = do
    let initialState = ResolverState{globalBindings = Map.empty, instanceBindings = Map.empty}
    let resolverM = runResolverM (analyzeTree root)
    let (result, finalState) = runState (runExceptT resolverM) initialState
    pure $ case result of
        Left err -> Left err
        Right expr -> Right (expr, globalBindings finalState, instanceBindings finalState)

runResolverWithEnv :: TypeEnv -> Expr -> IO (Either InferenceError (Expr, TypeEnv, InstanceEnv))
runResolverWithEnv initialEnv root = do
    let initialState = ResolverState{globalBindings = initialEnv, instanceBindings = Map.empty}
    let resolverM = runResolverM (analyzeTree root)
    let (result, finalState) = runState (runExceptT resolverM) initialState
    pure $ case result of
        Left err -> Left err
        Right expr -> Right (expr, globalBindings finalState, instanceBindings finalState)

replaceAllUnresolvedQualified :: Expr -> TypeEnv -> QualifiedType -> ResolverM QualifiedType
replaceAllUnresolvedQualified expr env (Forall vars constraints t) = do
    (finalTyp, qualifieds) <- replaceAllUnresolvedC t
    case qualifieds of
        [] -> pure $ Forall vars constraints finalTyp
        otherQualifiedTypes -> do
            let resolved = Forall vars constraints finalTyp
            let resolvedQualified = sumQualifiedTypes resolved otherQualifiedTypes
            pure resolvedQualified
  where
    replaceAllUnresolvedC :: Type -> ResolverM (Type, [QualifiedType])
    replaceAllUnresolvedC (TUnresolved name) =
        case Map.lookup name env of
            Just qual@(Forall _ _ resolvedType) -> pure (resolvedType, [qual])
            Nothing -> throwError $ UnknownTypeConstructor expr name
    replaceAllUnresolvedC t'@(TVar _) = pure (t', [])
    replaceAllUnresolvedC t'@(TSkolem _) = pure (t', [])
    replaceAllUnresolvedC (TConstructor tc) =
        pure (TConstructor tc, [])
    replaceAllUnresolvedC (TApp t1 t2) = do
        (t1', qu1) <- replaceAllUnresolvedC t1
        (t2', qu2) <- replaceAllUnresolvedC t2
        let newType = TApp t1' t2'
        let qualifieds = mconcat [qu1, qu2]
        pure (newType, qualifieds)
    replaceAllUnresolvedC (TArrow t1 t2) = do
        (t1', qu1) <- replaceAllUnresolvedC t1
        (t2', qu2) <- replaceAllUnresolvedC t2
        let newType = TArrow t1' t2'
        let qualifieds = mconcat [qu1, qu2]
        pure (newType, qualifieds)
