{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module Inference.Resolver where

import Control.Monad (forM_, when)
import Control.Monad.Reader (MonadReader (local), ReaderT (runReaderT), asks)
import Control.Monad.State (MonadState (get, put), State, gets, modify', runState)
import Control.Monad.Writer (MonadWriter (tell), WriterT (runWriterT))
import Data.Foldable (foldlM)
import Data.List (partition)
import qualified Data.Map as Map
import Inference.Core (InstanceEnv, TypeEnv)
import Inference.Errors (InferenceError (..))
import Inference.InstanceValidation (validateInstances)
import Lexing.Position (Located (..), Span (..))
import Project.Symbols (Symbol (..), SymbolKind (..))
import Project.Unique (Unique (..))
import Syntax.Patterns (ParsedPattern, Pattern (..))
import Syntax.Tree (ComposeStmt (..), Expr (..), exprChildren)
import Typing.Currying (curryFunction)
import Typing.Types (Constraint (..), Kind (..), QualifiedType (Forall), TyConstructor (TypeConstructor), TyUnique (..), TyVar (tvKind), Type (..), assignConstraints, primitiveFromName, sumQualifiedTypes)

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
    , uniqueCounter :: !Int
    , typeUniques :: !(Map.Map String TyUnique)
    }

type SymbolMap = Map.Map String Symbol

freshUnique :: String -> ResolverM Unique
freshUnique originalName = do
    st <- get
    let uid = uniqueCounter st
    let moduleName = currentModule st
    put st{uniqueCounter = uid + 1}
    pure
        Unique
            { uniqueId = uid
            , uniqueModule = moduleName
            , uniqueOriginal = originalName
            }

mkSymbol :: String -> SymbolKind -> Span -> ResolverM Symbol
mkSymbol name kind sySpan = do
    unique <- freshUnique name
    mkSymbolWithUnique unique name kind sySpan

mkSymbolWithUnique :: Unique -> String -> SymbolKind -> Span -> ResolverM Symbol
mkSymbolWithUnique unique name kind sySpan = do
    moduleName <- gets currentModule
    packageName <- gets currentPackage
    return
        $ ResolvedSymbol
            { resolvedSymbolUnique = Just unique
            , resolvedSymbolName = name
            , resolvedSymbolKind = kind
            , resolvedSymbolModule = moduleName
            , resolvedSymbolPackage = packageName
            , resolvedSymbolSpan = sySpan
            }

findSymbolByName :: String -> TypeEnv -> Maybe (Symbol, QualifiedType)
findSymbolByName name env =
    let matches = [(sym, qual) | (sym, qual) <- Map.toList env, resolvedSymbolName sym == name]
        (constructors, others) = partition (isConstructorSymbol . fst) matches
    in case constructors ++ others of
        (sym, qual) : _ -> Just (sym, qual)
        [] -> Nothing
  where
    isConstructorSymbol sym = case resolvedSymbolKind sym of
        DataConstructorSymbol _ -> True
        _ -> False

findTypeByName :: String -> TypeEnv -> Maybe (Symbol, QualifiedType)
findTypeByName name env =
    let matches = [(sym, qual) | (sym, qual) <- Map.toList env, resolvedSymbolName sym == name]
        (types, others) = partition (isTypeSymbol . fst) matches
    in case types ++ others of
        (sym, qual) : _ -> Just (sym, qual)
        [] -> Nothing
  where
    isTypeSymbol sym = case resolvedSymbolKind sym of
        TypeSymbol -> True
        TypeClassSymbol -> True
        IntrinsicTypeSymbol -> True
        _ -> False

collectGlobals :: Expr -> ResolverM ()
collectGlobals (ExprRoot children) = do
    mapM_ collectGlobals children
collectGlobals (ExprBindingDef{}) =
    pure ()
collectGlobals (ExprIntrinsicDef{}) = do
    pure ()
collectGlobals (ExprIntrinsicDataTypeDef name kind eSpan) = do
    tyUnique <- case primitiveFromName name of
        Just prim -> pure (TyPrim prim)
        Nothing -> TyUserDefined <$> freshUnique name
    modify' $ \s -> s{typeUniques = Map.insert name tyUnique (typeUniques s)}
    let baseConstructor = TConstructor $ TypeConstructor tyUnique kind
    let constrainedType = Forall [] [] baseConstructor
    addGlobalBinding name constrainedType IntrinsicTypeSymbol eSpan
collectGlobals (ExprDataTypeDef name generics constraints constructors _attrs eSpan) = do
    typeUnique <- freshUnique name
    let tyUnique = TyUserDefined typeUnique

    modify' $ \s -> s{typeUniques = Map.insert name tyUnique (typeUniques s)}

    let kind = foldr (KindArrow . tvKind) KindStar generics
    let baseConstructor = TConstructor $ TypeConstructor tyUnique kind

    let structType =
            if null generics
                then baseConstructor
                else foldl TApp baseConstructor (map TVar generics)

    let constrainedStructType = Forall generics constraints baseConstructor
    addGlobalBinding name constrainedStructType TypeSymbol eSpan

    forM_ constructors $ \constructor -> addConstructor name structType constrainedStructType constructor
  where
    addConstructor parentName structType constrainedStructType = \case
        ExprDataConstructor cName fields eSpan' -> do
            let fieldTypes = map (lValue . snd) fields
                curried = curryFunction fieldTypes structType
                qualified = assignConstraints constrainedStructType curried
            addGlobalBinding cName qualified (DataConstructorSymbol parentName) eSpan'
        recv -> error $ "Expected ExprDataTypeDef in ADT definition but got " ++ show recv
collectGlobals (ExprStructDef name generics constraints ctorName fields _attrs eSpan) = do
    typeUnique <- freshUnique name
    let tyUnique = TyUserDefined typeUnique

    modify' $ \s -> s{typeUniques = Map.insert name tyUnique (typeUniques s)}

    let kind = foldr (KindArrow . tvKind) KindStar generics
    let baseConstructor = TConstructor $ TypeConstructor tyUnique kind

    let structType =
            if null generics
                then baseConstructor
                else foldl TApp baseConstructor (map TVar generics)

    let constrainedStructType = Forall generics constraints baseConstructor
    typeSymbol <- mkSymbolWithUnique typeUnique name TypeSymbol eSpan
    addGlobalBindingWithSymbol typeSymbol constrainedStructType

    let fieldTypes = map (lValue . snd) fields
        curried = curryFunction fieldTypes structType
        qualified = assignConstraints constrainedStructType curried
    addGlobalBinding ctorName qualified (DataConstructorSymbol name) eSpan
collectGlobals (ExprTypeClassDef className (Located _ ty@(Forall generics _ _)) _ eSpan) = do
    classUnique <- freshUnique className
    let tyUnique = TyUserDefined classUnique
    modify' $ \s -> s{typeUniques = Map.insert className tyUnique (typeUniques s)}
    let kind = foldr (KindArrow . tvKind) KindStar generics
    let baseConstructor = TConstructor $ TypeConstructor tyUnique kind
    let finalTy = replaceUnresolvedWith ty baseConstructor
    addGlobalBinding className finalTy TypeClassSymbol eSpan
collectGlobals _ = pure ()

collectInstances :: Expr -> ResolverM ()
collectInstances (ExprRoot children) = do
    mapM_ collectInstances children
collectInstances (ExprInstanceDef constraintType _ _) = do
    addInstanceBindingFromType constraintType
collectInstances (ExprIntrinsicInstanceDef (Located _ constraintType) _) = do
    addInstanceBindingFromType constraintType
collectInstances expr = do
    mapM_ collectInstances (exprChildren expr)

resolveTReference :: Expr -> ResolverM Expr
resolveTReference (ExprRoot children) = do
    children' <- mapM resolveTReference children
    pure $ ExprRoot children'
resolveTReference (ExprDataTypeDef name generics constraints constructors attrs s) = do
    constructors' <- mapM resolveTReference constructors
    pure $ ExprDataTypeDef name generics constraints constructors' attrs s
resolveTReference expr@ExprStructDef{} = pure expr
resolveTReference (ExprTypeClassDef name (Located tySpan ty) methods s) = do
    let typeExpr = ExprNum "" tySpan
    ty' <- replaceAllUnresolvedQualified typeExpr ty
    methods' <-
        local (\env -> env{currentTypeClass = Just name})
            $ mapM resolveTReference methods
    pure $ ExprTypeClassDef name (Located tySpan ty') methods' s
resolveTReference (ExprTypeClassBinding name (Located typSpan typ) defaultV eSpan) = do
    let typeExpr = ExprNum "" typSpan
    realTyp <- replaceAllUnresolvedQualified typeExpr typ
    className <- asks currentTypeClass
    let symbolKind = case className of
            Just cn -> TypeClassMethodSymbol cn
            Nothing -> TypeClassMethodSymbol "Unknown"
    addGlobalBinding name realTyp symbolKind eSpan
    pure $ ExprTypeClassBinding name (Located typSpan realTyp) defaultV eSpan
resolveTReference expr@(ExprInstanceDef constraintType binds s) = do
    binds' <- mapM resolveTReference binds
    constraintType' <- replaceAllUnresolvedQualified expr constraintType
    pure $ ExprInstanceDef constraintType' binds' s
resolveTReference expr@(ExprIntrinsicInstanceDef (Located typSpan constraintType) s) = do
    constraintType' <- replaceAllUnresolvedQualified expr constraintType
    pure $ ExprIntrinsicInstanceDef (Located typSpan constraintType') s
resolveTReference (ExprBindingDef name (Located typSpan typ) body topLevel mods eSpan) = do
    let typeExpr = ExprNum "" typSpan -- Dummy expression with the type's span
    realTyp <- replaceAllUnresolvedQualified typeExpr typ
    body' <- resolveTReference body
    when topLevel $ do
        addGlobalBinding name realTyp (BindingSymbol realTyp) eSpan

    pure $ ExprBindingDef name (Located typSpan realTyp) body' topLevel mods eSpan
resolveTReference (ExprIntrinsicDef name (Located typSpan typ) eSpan) = do
    let typeExpr = ExprNum "" typSpan
    realTyp <- replaceAllUnresolvedQualified typeExpr typ
    addGlobalBinding name realTyp IntrinsicBindingSymbol eSpan
    pure $ ExprIntrinsicDef name (Located typSpan realTyp) eSpan
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
resolveTReference (ExprIf condition thenBranch elseBranch eSpan) = do
    condition' <- resolveTReference condition
    thenBranch' <- resolveTReference thenBranch
    elseBranch' <- resolveTReference elseBranch
    pure $ ExprIf condition' thenBranch' elseBranch' eSpan
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
    collectPatternSymbol :: ParsedPattern -> ResolverM SymbolMap
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
    symbol <- mkSymbol name kind sySpan
    addGlobalBindingWithSymbol symbol ty

addGlobalBindingWithSymbol :: Symbol -> QualifiedType -> ResolverM ()
addGlobalBindingWithSymbol symbol ty = do
    oldGlobals <- gets globalBindings
    let name = resolvedSymbolName symbol
        kind = resolvedSymbolKind symbol
    -- Only remove existing symbols with the same name AND same kind category
    -- This allows type symbols and constructor symbols with the same name to coexist
    let globals' = Map.filterWithKey (\sym _ -> not (shouldReplace sym name kind)) oldGlobals
        newGlobals = Map.insert symbol ty globals'
    modify' $ \s -> s{globalBindings = newGlobals}
  where
    shouldReplace sym symName symKind =
        resolvedSymbolName sym == symName && sameKindCategory (resolvedSymbolKind sym) symKind
    sameKindCategory :: SymbolKind -> SymbolKind -> Bool
    sameKindCategory TypeSymbol TypeSymbol = True
    sameKindCategory TypeClassSymbol TypeClassSymbol = True
    sameKindCategory IntrinsicTypeSymbol IntrinsicTypeSymbol = True
    sameKindCategory (DataConstructorSymbol _) (DataConstructorSymbol _) = True
    sameKindCategory (BindingSymbol _) (BindingSymbol _) = True
    sameKindCategory IntrinsicBindingSymbol IntrinsicBindingSymbol = True
    sameKindCategory PatternVariableSymbol PatternVariableSymbol = True
    sameKindCategory _ _ = False

addInstanceBindingFromType :: QualifiedType -> ResolverM ()
addInstanceBindingFromType constraintType = do
    s <- get
    let instances = instanceBindings s
    put s{instanceBindings = Map.insert constraintType True instances}

runResolver :: String -> String -> Expr -> ([InferenceError], (Expr, TypeEnv, InstanceEnv))
runResolver packageName moduleName expr =
    let (errors, (resolvedExpr, tyEnv, instEnv, _counter)) = runResolverWithEnv packageName moduleName Map.empty Map.empty expr
    in (errors, (resolvedExpr, tyEnv, instEnv))

runResolverWithEnv :: String -> String -> TypeEnv -> InstanceEnv -> Expr -> ([InferenceError], (Expr, TypeEnv, InstanceEnv, Int))
runResolverWithEnv packageName moduleName initialTyEnv initialInstEnv root = do
    let initialState =
            ResolverState
                { globalBindings = initialTyEnv
                , instanceBindings = initialInstEnv
                , currentModule = moduleName
                , currentPackage = packageName
                , uniqueCounter = 0
                , typeUniques = Map.empty
                }
    let initialEnv =
            ResolverEnv
                { localScope = Map.empty
                , currentTypeClass = Nothing
                }
    let resolverM = runResolverM (analyzeTree root)
    let ((expr, errors), finalState) = runState (runWriterT (runReaderT resolverM initialEnv)) initialState
    (errors, (expr, globalBindings finalState, instanceBindings finalState, uniqueCounter finalState))

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
        case primitiveFromName name of
            Just prim -> do
                let tc = TypeConstructor (TyPrim prim) KindStar
                pure (TConstructor tc, [])
            Nothing -> do
                env <- getEnv
                case findTypeByName name env of
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
