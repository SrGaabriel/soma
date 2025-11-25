{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module Inference.Resolver where

import Control.Monad (when)
import Control.Monad.Reader (MonadReader (local), ReaderT (runReaderT), asks)
import Control.Monad.State (MonadState (get, put), State, gets, runState)
import Control.Monad.Writer (MonadWriter (tell), WriterT (runWriterT))
import Data.Foldable (foldlM)
import qualified Data.Map as Map
import Inference.Core (InstanceEnv, TypeEnv)
import Inference.Errors (InferenceError (..))
import Inference.InstanceValidation (validateInstances)
import Lexing.Position (Span (..))
import Project.Symbols (Symbol (..), SymbolKind (..))
import Syntax.Patterns (Pattern (..))
import Syntax.Tree (ComposeStmt (..), Expr (..), exprChildren)
import Typing.Currying (curryFunction)
import Typing.Types (Constraint (..), Kind (..), QualifiedType (Forall), TyConstructor (TypeConstructor), TyVar (tvKind), Type (..), assignConstraints, sumQualifiedTypes)

newtype ResolverM a = ResolverM
    { runResolverM :: ReaderT ResolverEnv (WriterT [InferenceError] (State ResolverState)) a
    }
    deriving
        ( Functor
        , Applicative
        , Monad
        , MonadState ResolverState
        , MonadWriter [InferenceError]
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
    addGlobalBinding name constrainedStructType TypeSymbol eSpan

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
collectGlobals (ExprTypeClassDef className ty@(Forall generics _ _) _ eSpan) = do
    let kind = foldr (KindArrow . tvKind) KindStar generics
    let baseConstructor = TConstructor $ TypeConstructor className kind
    let finalTy = replaceUnresolvedWith ty baseConstructor
    addGlobalBinding className finalTy TypeClassSymbol eSpan
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
resolveTReference expr@(ExprTypeClassDef name ty methods s) = do
    ty' <- replaceAllUnresolvedQualified expr ty
    methods' <-
        local (\env -> env{currentTypeClass = Just name})
            $ mapM resolveTReference methods
    pure $ ExprTypeClassDef name ty' methods' s
resolveTReference expr@(ExprTypeClassBinding name typ defaultV eSpan) = do
    realTyp <- replaceAllUnresolvedQualified expr typ
    className <- asks currentTypeClass
    let symbolKind = case className of
            Just cn -> TypeClassMethodSymbol cn
            Nothing -> TypeClassMethodSymbol "Unknown"
    addGlobalBinding name realTyp symbolKind eSpan
    pure $ ExprTypeClassBinding name realTyp defaultV eSpan
resolveTReference expr@(ExprInstanceDef constraintType binds s) = do
    binds' <- mapM resolveTReference binds
    Forall _ _ constraintType' <- replaceAllUnresolvedQualified expr (Forall [] [] constraintType)
    pure $ ExprInstanceDef constraintType' binds' s
resolveTReference expr@(ExprBindingDef name typ body topLevel eSpan) = do
    realTyp <- replaceAllUnresolvedQualified expr typ
    body' <- resolveTReference body
    when topLevel $ do
        addGlobalBinding name realTyp (BindingSymbol realTyp) eSpan

    pure $ ExprBindingDef name realTyp body' topLevel eSpan
resolveTReference expr@(ExprIntrinsicDef name typ eSpan) = do
    realTyp <- replaceAllUnresolvedQualified expr typ
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
                Nothing -> do
                    tell [UnboundVariable expr name]
                    pure expr
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
                body' <-
                    local (\env -> env{localScope = Map.union accMap (localScope env)})
                        $ resolveTReference body
                let newMap = Map.insert name symbol accMap
                pure (CSBind name body' cSpan : accStmts, newMap)
            CSLet name body cSpan -> do
                symbol <- mkSymbol name LetBindingSymbol cSpan
                body' <-
                    local (\env -> env{localScope = Map.union accMap (localScope env)})
                        $ resolveTReference body
                let newMap = Map.insert name symbol accMap
                pure (CSLet name body' cSpan : accStmts, newMap)
            CSExpr e cSpan -> do
                e' <-
                    local (\env -> env{localScope = Map.union accMap (localScope env)})
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

analyzeTree :: Expr -> ResolverM Expr
analyzeTree root = do
    collectGlobals root
    resolved <- resolveTReference root
    collectInstances resolved

    instEnv <- getInstanceEnv
    tell (validateInstances instEnv resolved)

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

runResolver :: String -> String -> Expr -> ([InferenceError], (Expr, TypeEnv, InstanceEnv))
runResolver packageName moduleName = runResolverWithEnv packageName moduleName Map.empty Map.empty

runResolverWithEnv :: String -> String -> TypeEnv -> InstanceEnv -> Expr -> ([InferenceError], (Expr, TypeEnv, InstanceEnv))
runResolverWithEnv packageName moduleName initialTyEnv initialInstEnv root = do
    let initialState =
            ResolverState
                { globalBindings = initialTyEnv
                , instanceBindings = initialInstEnv
                , currentModule = moduleName
                , currentPackage = packageName
                }
    let initialEnv =
            ResolverEnv
                { localScope = Map.empty
                , currentTypeClass = Nothing
                }
    let resolverM = runResolverM (analyzeTree root)
    let ((expr, errors), finalState) = runState (runWriterT (runReaderT resolverM initialEnv)) initialState
    (errors, (expr, globalBindings finalState, instanceBindings finalState))

replaceAllUnresolvedQualified :: Expr -> QualifiedType -> ResolverM QualifiedType
replaceAllUnresolvedQualified expr (Forall vars constraints t) = do
    (finalTyp, qualifieds) <- replaceAllUnresolvedC t
    resolvedConstraints <- mapM resolveConstraint constraints

    case qualifieds of
        [] -> pure $ Forall vars resolvedConstraints finalTyp
        otherQualifiedTypes -> do
            let resolved = Forall vars resolvedConstraints finalTyp
            let resolvedQualified = sumQualifiedTypes resolved otherQualifiedTypes
            pure resolvedQualified
  where
    resolveConstraint :: Constraint -> ResolverM Constraint
    resolveConstraint (Constraint constraintType) = do
        (resolvedType, _) <- replaceAllUnresolvedC constraintType
        case containsUnresolved resolvedType of
            Just unresolvedName -> do
                tell [UnknownTrait expr unresolvedName]
                pure $ Constraint resolvedType
            Nothing -> pure $ Constraint resolvedType

    containsUnresolved :: Type -> Maybe String
    containsUnresolved (TUnresolved name) = Just name
    containsUnresolved (TApp t1 t2) = containsUnresolved t1 `orElse` containsUnresolved t2
    containsUnresolved (TArrow t1 t2) = containsUnresolved t1 `orElse` containsUnresolved t2
    containsUnresolved _ = Nothing

    orElse :: Maybe a -> Maybe a -> Maybe a
    orElse (Just x) _ = Just x
    orElse Nothing y = y

    getHeadConstructor :: Type -> Type
    getHeadConstructor (TApp t' _) = getHeadConstructor t'
    getHeadConstructor t' = t'

    replaceAllUnresolvedC :: Type -> ResolverM (Type, [QualifiedType])
    replaceAllUnresolvedC (TUnresolved name) = do
        env <- getEnv
        case findSymbolByName name env of
            Just (sym, qual@(Forall _ _ resolvedType)) -> do
                case resolvedSymbolKind sym of
                    TypeSymbol ->
                        pure (getHeadConstructor resolvedType, [])
                    TypeClassSymbol ->
                        pure (getHeadConstructor resolvedType, [])
                    IntrinsicTypeSymbol ->
                        pure (getHeadConstructor resolvedType, [])
                    _ -> pure (resolvedType, [qual])
            Nothing -> do
                tell [UnknownTypeConstructor expr name]
                pure (TUnresolved name, [])
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

replaceUnresolvedWith :: QualifiedType -> Type -> QualifiedType
replaceUnresolvedWith (Forall vars constraints baseTy) r =
    Forall vars constraints (replaceUnresolvedWith' baseTy r)
  where
    replaceUnresolvedWith' (TUnresolved{}) replacement = replacement
    replaceUnresolvedWith' t@(TVar{}) _ = t
    replaceUnresolvedWith' t@(TSkolem{}) _ = t
    replaceUnresolvedWith' t@(TConstructor{}) _ = t
    replaceUnresolvedWith' (TApp t1 t2) replacement =
        TApp (replaceUnresolvedWith' t1 replacement) (replaceUnresolvedWith' t2 replacement)
    replaceUnresolvedWith' (TArrow t1 t2) replacement =
        TArrow (replaceUnresolvedWith' t1 replacement) (replaceUnresolvedWith' t2 replacement)
