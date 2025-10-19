{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module Inference.Resolver where

import Control.Monad (when)
import Control.Monad.Except (ExceptT, MonadError (throwError), runExceptT)
import Control.Monad.State (MonadState (get, put), State, gets, modify, runState)
import qualified Data.Map as Map
import Inference.Core (InstanceEnv, TypeEnv)
import Inference.Errors (InferenceError (..))
import Inference.Substitution (Substitutable (apply))
import Lexing.Position (Span (..))
import Project.Symbols (Symbol (..), SymbolKind (..))
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
    , currentModule :: String
    , localScope :: [String]
    , currentTypeClass :: Maybe String
    }

createGlobalSymbol :: String -> SymbolKind -> ResolverM Symbol
createGlobalSymbol name kind = do
    moduleName <- gets currentModule
    return
        $ ResolvedSymbol
            { resolvedSymbolName = name
            , resolvedSymbolKind = kind
            , resolvedSymbolModule = moduleName
            , resolvedSymbolSpan = Span 0 0
            }

findSymbolByName :: String -> TypeEnv -> Maybe (Symbol, QualifiedType)
findSymbolByName name env =
    let matches = [(sym, qual) | (sym, qual) <- Map.toList env, resolvedSymbolName sym == name]
    in case matches of
        (sym, qual) : _ -> Just (sym, qual)
        [] -> Nothing

collectGlobals :: Expr -> ResolverM ()
collectGlobals (ExprRoot children) = do
    mapM_ collectGlobals children
collectGlobals (ExprBindingDef name bindType _ topLevel _) =
    when topLevel $ do
        addGlobalBinding name bindType BindingSymbol
collectGlobals (ExprIntrinsicDef name bindType _) = do
    addGlobalBinding name bindType IntrinsicBindingSymbol
collectGlobals (ExprIntrinsicDataTypeDef name kind _) = do
    let baseConstructor = TConstructor $ TypeConstructor name kind
    let constrainedType = Forall [] [] baseConstructor
    addGlobalBinding name constrainedType IntrinsicTypeSymbol
collectGlobals (ExprDataTypeDef name generics constraints constructors _) = do
    let kind = foldr (KindArrow . tvKind) KindStar generics
    let baseConstructor = TConstructor $ TypeConstructor name kind

    let structType =
            if null generics
                then baseConstructor
                else foldl TApp baseConstructor (map TVar generics)

    let constrainedStructType = Forall generics constraints structType
    addGlobalBinding name constrainedStructType (TypeSymbol (length generics))

    mapM_
        ( \case
            ExprDataConstructor cName fields _ ->
                let fieldTypes = map snd fields
                    curried = curryFunction fieldTypes structType
                    qualified = assignConstraints constrainedStructType curried
                in addGlobalBinding cName qualified (DataConstructorSymbol name)
            recv -> error $ "Expected StructConstructorExpr in struct definition but got " ++ show recv
        )
        constructors
collectGlobals _ = pure ()

collectInstances :: Expr -> ResolverM ()
collectInstances (ExprRoot children) = do
    mapM_ collectInstances children
collectInstances (ExprInstanceDef constraintType _ _) = do
    addInstanceBindingFromType constraintType
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
    modify $ \st -> st{currentTypeClass = Just name}
    methods' <- mapM resolveTReference methods
    modify $ \st -> st{currentTypeClass = Nothing}
    pure $ ExprTypeClassDef name generics methods' s
resolveTReference expr@(ExprTypeClassBinding name typ defaultV s) = do
    env <- getEnv
    realTyp <- replaceAllUnresolvedQualified expr env typ
    className <- gets currentTypeClass
    let symbolKind = case className of
            Just cn -> TypeClassMethodSymbol cn
            Nothing -> TypeClassMethodSymbol "Unknown"
    addGlobalBinding name realTyp symbolKind
    pure $ ExprTypeClassBinding name realTyp defaultV s
resolveTReference (ExprInstanceDef constraintType binds s) = do
    binds' <- mapM resolveTReference binds
    pure $ ExprInstanceDef constraintType binds' s
resolveTReference expr@(ExprBindingDef a typ body topLevel c) = do
    env <- getEnv
    realTyp <- replaceAllUnresolvedQualified expr env typ
    body' <- resolveTReference body
    when topLevel $ do
        addGlobalBinding a realTyp BindingSymbol

    pure $ ExprBindingDef a realTyp body' topLevel c
resolveTReference expr@(ExprIntrinsicDef name typ s) = do
    env <- getEnv
    realTyp <- replaceAllUnresolvedQualified expr env typ
    addGlobalBinding name realTyp IntrinsicBindingSymbol
    pure $ ExprIntrinsicDef name realTyp s
resolveTReference (ExprUVar name varSpan) = do
    state <- get
    if name `elem` localScope state
        then pure $ ExprUVar name varSpan
        else do
            env <- getEnv
            case findSymbolByName name env of
                Just (symbol, _) -> pure $ ExprVar symbol varSpan
                Nothing ->
                    pure $ ExprUVar name varSpan
resolveTReference expr = do
    case expr of
        ExprApp f a -> do
            f' <- resolveTReference f
            a' <- resolveTReference a
            pure $ ExprApp f' a'
        ExprLambda args body exprSpan -> do
            modify $ \s -> s{localScope = localScope s ++ args}
            body' <- resolveTReference body
            modify $ \s -> s{localScope = drop (length args) (localScope s)}
            pure $ ExprLambda args body' exprSpan
        ExprLet name value body exprSpan -> do
            value' <- resolveTReference value
            body' <- resolveTReference body
            pure $ ExprLet name value' body' exprSpan
        ExprPatternMatch scrutinee arms exprSpan -> do
            scrutinee' <- resolveTReference scrutinee
            arms' <- mapM resolveTReference arms
            pure $ ExprPatternMatch scrutinee' arms' exprSpan
        ExprDerivedPatternMatch arms -> do
            arms' <- mapM resolveTReference arms
            pure $ ExprDerivedPatternMatch arms'
        ExprPatternMatchArm patterns body exprSpan -> do
            body' <- resolveTReference body
            pure $ ExprPatternMatchArm patterns body' exprSpan
        ExprBlock exprs exprSpan -> do
            exprs' <- mapM resolveTReference exprs
            pure $ ExprBlock exprs' exprSpan
        ExprArray exprs exprSpan -> do
            exprs' <- mapM resolveTReference exprs
            pure $ ExprArray exprs' exprSpan
        ExprTuple exprs exprSpan -> do
            exprs' <- mapM resolveTReference exprs
            pure $ ExprTuple exprs' exprSpan
        _ -> pure expr

getEnv :: ResolverM TypeEnv
getEnv = gets globalBindings

getInstanceEnv :: ResolverM InstanceEnv
getInstanceEnv = gets instanceBindings

getReference :: Expr -> String -> ResolverM QualifiedType
getReference expr name = do
    s <- get
    case findSymbolByName name (globalBindings s) of
        Just (_, ty) -> pure ty
        Nothing -> throwError $ UnknownTypeConstructor expr name

analyzeTree :: Expr -> ResolverM Expr
analyzeTree root = do
    collectGlobals root
    collectInstances root
    resolveTReference root

addGlobalBinding :: String -> QualifiedType -> SymbolKind -> ResolverM ()
addGlobalBinding name ty kind = do
    s <- get
    let globals = globalBindings s
    symbol <- createGlobalSymbol name kind
    put s{globalBindings = Map.insert symbol ty globals}

addInstanceBindingFromType :: Type -> ResolverM ()
addInstanceBindingFromType constraintType = do
    s <- get
    let instances = instanceBindings s
    put s{instanceBindings = Map.insert constraintType True instances}

runResolver :: String -> Expr -> IO (Either InferenceError (Expr, TypeEnv, InstanceEnv))
runResolver moduleName root = do
    let initialState = ResolverState{globalBindings = Map.empty, instanceBindings = Map.empty, currentModule = moduleName, localScope = [], currentTypeClass = Nothing}
    let resolverM = runResolverM (analyzeTree root)
    let (result, finalState) = runState (runExceptT resolverM) initialState
    pure $ case result of
        Left err -> Left err
        Right expr -> Right (expr, globalBindings finalState, instanceBindings finalState)

runResolverWithEnv :: String -> TypeEnv -> Expr -> IO (Either InferenceError (Expr, TypeEnv, InstanceEnv))
runResolverWithEnv moduleName initialEnv root = do
    let initialState = ResolverState{globalBindings = initialEnv, instanceBindings = Map.empty, currentModule = moduleName, localScope = [], currentTypeClass = Nothing}
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
        case findSymbolByName name env of
            Just (_, qual@(Forall _ _ resolvedType)) -> pure (resolvedType, [qual])
            Nothing -> throwError $ UnknownTypeConstructor expr name
    replaceAllUnresolvedC t'@(TVar _) = pure (t', [])
    replaceAllUnresolvedC t'@(TSkolem _) = pure (t', [])
    replaceAllUnresolvedC (TConstructor tc) =
        pure (TConstructor tc, [])
    replaceAllUnresolvedC (TApp t1 t2) = do
        (t1', qu1) <- replaceAllUnresolvedC t1
        (t2', qu2) <- replaceAllUnresolvedC t2

        case (t1, qu1) of
            (TUnresolved _, [Forall (tv : _) _ _]) -> do
                let subst = Map.singleton tv t2'
                let instantiatedType = apply subst t1'
                pure (instantiatedType, [])
            _ -> do
                let newType = TApp t1' t2'
                let qualifieds = mconcat [qu1, qu2]
                pure (newType, qualifieds)
    replaceAllUnresolvedC (TArrow t1 t2) = do
        (t1', qu1) <- replaceAllUnresolvedC t1
        (t2', qu2) <- replaceAllUnresolvedC t2
        let newType = TArrow t1' t2'
        let qualifieds = mconcat [qu1, qu2]
        pure (newType, qualifieds)
