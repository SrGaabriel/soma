{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module Inference.Resolver where

import Control.Monad (when)
import Control.Monad.Except (ExceptT, MonadError (throwError), runExceptT)
import Control.Monad.Reader (MonadReader (local), ReaderT (runReaderT), asks)
import Control.Monad.State (MonadState (get, put), State, gets, runState)
import qualified Data.Map as Map
import Inference.Core (InstanceEnv, TypeEnv)
import Inference.Errors (InferenceError (..))
import Lexing.Position (Span (..))
import Project.Symbols (Symbol (..), SymbolKind (..))
import Syntax.Patterns (Pattern (..))
import Syntax.Tree (ComposeStmt (..), Expr (..), exprChildren)
import Typing.Currying (curryFunction)
import Typing.Types (Kind (..), QualifiedType (Forall), TyConstructor (TypeConstructor), TyVar (tvKind), Type (..), assignConstraints, sumQualifiedTypes)
import Data.Foldable (foldlM)

newtype ResolverM a = ResolverM
    { runResolverM :: ReaderT ResolverEnv (ExceptT InferenceError (State ResolverState)) a
    }
    deriving
        ( Functor
        , Applicative
        , Monad
        , MonadState ResolverState
        , MonadError InferenceError
        , MonadReader ResolverEnv
        )

data ResolverEnv = ResolverEnv
    { localScope :: SymbolMap
    , currentTypeClass :: Maybe String
    }

data ResolverState = ResolverState
    { globalBindings :: TypeEnv
    , instanceBindings :: InstanceEnv
    , currentModule :: String
    , currentPackage :: String
    }

type SymbolMap = Map.Map String Symbol

mkSymbol :: String -> SymbolKind -> Span -> ResolverM Symbol
mkSymbol name kind sySpan = do
    moduleName <- gets currentModule
    packageName <- gets currentPackage
    return
        $ ResolvedSymbol
            { resolvedSymbolName = name
            , resolvedSymbolKind = kind
            , resolvedSymbolModule = moduleName
            , resolvedSymbolPackage = packageName
            , resolvedSymbolSpan = sySpan
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
collectGlobals (ExprBindingDef name bindType _ topLevel eSpan) =
    when topLevel $ do
        addGlobalBinding name bindType (BindingSymbol bindType) eSpan
collectGlobals (ExprIntrinsicDef name bindType eSpan) = do
    addGlobalBinding name bindType IntrinsicBindingSymbol eSpan
collectGlobals (ExprIntrinsicDataTypeDef name kind eSpan) = do
    let baseConstructor = TConstructor $ TypeConstructor name kind
    let constrainedType = Forall [] [] baseConstructor
    addGlobalBinding name constrainedType IntrinsicTypeSymbol eSpan
collectGlobals (ExprDataTypeDef name generics constraints constructors eSpan) = do
    let kind = foldr (KindArrow . tvKind) KindStar generics
    let baseConstructor = TConstructor $ TypeConstructor name kind

    let structType =
            if null generics
                then baseConstructor
                else foldl TApp baseConstructor (map TVar generics)

    let constrainedStructType = Forall generics constraints baseConstructor
    addGlobalBinding name constrainedStructType (TypeSymbol (length generics)) eSpan

    mapM_
        ( \case
            ExprDataConstructor cName fields eSpan' ->
                let fieldTypes = map snd fields
                    curried = curryFunction fieldTypes structType
                    qualified = assignConstraints constrainedStructType curried
                in addGlobalBinding cName qualified (DataConstructorSymbol name) eSpan'
            recv -> error $ "Expected StructConstructorExpr in struct definition but got " ++ show recv
        )
        constructors
collectGlobals (ExprTypeClassDef className generics _ eSpan) = do
    let kind = foldr (KindArrow . tvKind) KindStar generics
    let baseConstructor = TConstructor $ TypeConstructor className kind
    addGlobalBinding className (Forall generics [] baseConstructor) TypeClassSymbol eSpan
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
    methods' <-
        local (\env -> env{currentTypeClass = Just name})
            $ mapM resolveTReference methods
    pure $ ExprTypeClassDef name generics methods' s
resolveTReference expr@(ExprTypeClassBinding name typ defaultV eSpan) = do
    env <- getEnv
    realTyp <- replaceAllUnresolvedQualified expr env typ
    className <- asks currentTypeClass
    let symbolKind = case className of
            Just cn -> TypeClassMethodSymbol cn
            Nothing -> TypeClassMethodSymbol "Unknown"
    addGlobalBinding name realTyp symbolKind eSpan
    pure $ ExprTypeClassBinding name realTyp defaultV eSpan
resolveTReference expr@(ExprInstanceDef constraintType binds s) = do
    env <- getEnv
    binds' <- mapM resolveTReference binds
    Forall _ _ constraintType' <- replaceAllUnresolvedQualified expr env (Forall [] [] constraintType)
    pure $ ExprInstanceDef constraintType' binds' s
resolveTReference expr@(ExprBindingDef name typ body topLevel eSpan) = do
    env <- getEnv
    realTyp <- replaceAllUnresolvedQualified expr env typ
    body' <- resolveTReference body
    when topLevel $ do
        addGlobalBinding name realTyp (BindingSymbol realTyp) eSpan

    pure $ ExprBindingDef name realTyp body' topLevel eSpan
resolveTReference expr@(ExprIntrinsicDef name typ eSpan) = do
    env <- getEnv
    realTyp <- replaceAllUnresolvedQualified expr env typ
    addGlobalBinding name realTyp IntrinsicBindingSymbol eSpan
    pure $ ExprIntrinsicDef name realTyp eSpan
resolveTReference expr@(ExprUVar name varSpan) = do
    scope <- asks localScope
    case Map.lookup name scope of
        Just symbol -> pure $ ExprVar symbol varSpan
        Nothing -> do
            tyEnv <- getEnv
            case findSymbolByName name tyEnv of
                Just (symbol, _) -> pure $ ExprVar symbol varSpan
                Nothing -> throwError $ UnboundVariable expr name
resolveTReference (ExprApp f a) = do
    f' <- resolveTReference f
    a' <- resolveTReference a
    pure $ ExprApp f' a'
resolveTReference (ExprLambda args body eSpan) = do
    argSymbols <-
        Map.fromList
            <$> mapM
                ( \n -> do
                    sym <- mkSymbol n LambdaParameterSymbol eSpan
                    return (n, sym)
                )
                args
    body' <-
        local (\env -> env{localScope = Map.union argSymbols (localScope env)})
            $ resolveTReference body
    pure $ ExprLambda args body' eSpan
resolveTReference (ExprLet name value body eSpan) = do
    value' <- resolveTReference value
    letSymbol <- mkSymbol name LetBindingSymbol eSpan
    body' <-
        local
            ( \env ->
                env
                    { localScope = Map.insert name letSymbol (localScope env)
                    }
            )
            $ resolveTReference body
    pure $ ExprLet name value' body' eSpan
resolveTReference (ExprPatternMatch scrutinee arms eSpan) = do
    scrutinee' <- resolveTReference scrutinee
    arms' <- mapM resolveTReference arms
    pure $ ExprPatternMatch scrutinee' arms' eSpan
resolveTReference (ExprDerivedPatternMatch arms) = do
    arms' <- mapM resolveTReference arms
    pure $ ExprDerivedPatternMatch arms'
resolveTReference expr@(ExprPatternMatchArm patterns body eSpan) = do
    symbols <- collectPatternMatchArmSymbols expr
    let extendEnv = Map.union symbols
    body' <- local (\env -> env{localScope = extendEnv (localScope env)}) $ resolveTReference body
    pure $ ExprPatternMatchArm patterns body' eSpan
resolveTReference (ExprBlock exprs eSpan) = do
    exprs' <- mapM resolveTReference exprs
    pure $ ExprBlock exprs' eSpan
resolveTReference (ExprArray exprs eSpan) = do
    exprs' <- mapM resolveTReference exprs
    pure $ ExprArray exprs' eSpan
resolveTReference (ExprTuple exprs eSpan) = do
    exprs' <- mapM resolveTReference exprs
    pure $ ExprTuple exprs' eSpan
resolveTReference (ExprCompose stmts eSpan) = do
    (stmts', _) <- foldlM go ([], Map.empty) stmts
    pure $ ExprCompose (reverse stmts') eSpan
  where
    go :: ([ComposeStmt], SymbolMap) -> ComposeStmt -> ResolverM ([ComposeStmt], SymbolMap)
    go (accStmts, accMap) stmt =
        case stmt of
            CSBind name body cSpan -> do
                symbol <- mkSymbol name ComposeBindingSymbol cSpan
                -- Use accMap to extend the environment when resolving body
                body' <- local (\env -> env{localScope = Map.union accMap (localScope env)}) 
                       $ resolveTReference body
                let newMap = Map.insert name symbol accMap
                pure (CSBind name body' cSpan : accStmts, newMap)

            CSLet name body cSpan -> do
                symbol <- mkSymbol name LetBindingSymbol cSpan
                -- Use accMap to extend the environment when resolving body
                body' <- local (\env -> env{localScope = Map.union accMap (localScope env)}) 
                       $ resolveTReference body
                let newMap = Map.insert name symbol accMap
                pure (CSLet name body' cSpan : accStmts, newMap)

            CSExpr e cSpan -> do
                -- Use accMap to extend the environment when resolving expression
                e' <- local (\env -> env{localScope = Map.union accMap (localScope env)}) 
                    $ resolveTReference e
                pure (CSExpr e' cSpan : accStmts, accMap)
resolveTReference expr = pure expr

collectPatternMatchArmSymbols :: Expr -> ResolverM SymbolMap
collectPatternMatchArmSymbols (ExprPatternMatchArm patterns _ _) = do
    symbolsList <- mapM collectPatternSymbol patterns
    pure $ Map.unions symbolsList
  where
    collectPatternSymbol :: Pattern -> ResolverM SymbolMap
    collectPatternSymbol (PVar name pSpan) = do
        sym <- mkSymbol name PatternVariableSymbol pSpan
        pure $ Map.singleton name sym
    collectPatternSymbol (PAs name pattern' pSpan) = do
        sym <- mkSymbol name PatternAsSymbol pSpan
        symbols <- collectPatternSymbol pattern'
        pure $ Map.insert name sym symbols
    collectPatternSymbol (PTuple patterns' _) = do
        symbols <- mapM collectPatternSymbol patterns'
        pure $ Map.unions symbols
    collectPatternSymbol (PConstructor _ patterns' _) = do
        symbols <- mapM collectPatternSymbol patterns'
        pure $ Map.unions symbols
    collectPatternSymbol _ = pure Map.empty
collectPatternMatchArmSymbols _ = pure Map.empty

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
    resolved <- resolveTReference root
    collectInstances resolved
    pure resolved

addGlobalBinding :: String -> QualifiedType -> SymbolKind -> Span -> ResolverM ()
addGlobalBinding name ty kind sySpan = do
    s <- get
    let globals = globalBindings s
    symbol <- mkSymbol name kind sySpan
    let globals' = Map.filterWithKey (\sym _ -> resolvedSymbolName sym /= name) globals
    put s{globalBindings = Map.insert symbol ty globals'}

addInstanceBindingFromType :: Type -> ResolverM ()
addInstanceBindingFromType constraintType = do
    s <- get
    let instances = instanceBindings s
    put s{instanceBindings = Map.insert constraintType True instances}

runResolver :: String -> String -> Expr -> IO (Either InferenceError (Expr, TypeEnv, InstanceEnv))
runResolver packageName moduleName root = do
    let initialState =
            ResolverState
                { globalBindings = Map.empty
                , instanceBindings = Map.empty
                , currentModule = moduleName
                , currentPackage = packageName
                }
    let initialEnv =
            ResolverEnv
                { localScope = Map.empty
                , currentTypeClass = Nothing
                }
    let resolverM = runResolverM (analyzeTree root)
    let (result, finalState) = runState (runExceptT (runReaderT resolverM initialEnv)) initialState
    pure $ case result of
        Left err -> Left err
        Right expr -> Right (expr, globalBindings finalState, instanceBindings finalState)

runResolverWithEnv :: String -> String -> TypeEnv -> Expr -> IO (Either InferenceError (Expr, TypeEnv, InstanceEnv))
runResolverWithEnv packageName moduleName initialTyEnv root = do
    let initialState =
            ResolverState
                { globalBindings = initialTyEnv
                , instanceBindings = Map.empty
                , currentModule = moduleName
                , currentPackage = packageName
                }
    let initialEnv =
            ResolverEnv
                { localScope = Map.empty
                , currentTypeClass = Nothing
                }
    let resolverM = runResolverM (analyzeTree root)
    let (result, finalState) = runState (runExceptT (runReaderT resolverM initialEnv)) initialState
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

        let newType = TApp t1' t2'
        let qualifieds = mconcat [qu1, qu2]
        pure (newType, qualifieds)
    replaceAllUnresolvedC (TArrow t1 t2) = do
        (t1', qu1) <- replaceAllUnresolvedC t1
        (t2', qu2) <- replaceAllUnresolvedC t2
        let newType = TArrow t1' t2'
        let qualifieds = mconcat [qu1, qu2]
        pure (newType, qualifieds)
