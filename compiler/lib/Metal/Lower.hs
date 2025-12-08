{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}

module Metal.Lower (
    lowerModule,
    LowerResult (..),
    lowerExpr,
    lowerBindingBody,
    runLower,
    LowerM,
    LowerState (..),
    symbolToName,
    untypedToInference,
) where

import Control.Monad (zipWithM)
import Control.Monad.State
import qualified Data.Map as Map
import Lexing.Position (Located (..), Span (..), dummySpan, spanBetween)
import Metal.Expr hiding (exprSpan)
import Metal.Metadata (FunctionAttributes (..), MetallicConstructorMetadata (..), MetallicTypeClassMetadata (..), defaultFunctionAttributes)
import Metal.Module (MetallicConstructor (..), MetallicTypeDef (..))
import Project.Name (Name (..))
import Project.Symbols (Symbol (..), SymbolKind (..))
import Project.Unique (Unique (..))
import Syntax.Patterns (ParsedPattern, Pattern (..), ResolvedPattern)
import Syntax.Tree (Attribute (..), ComposeStmt (..), Expr (..), exprSpan, uncurryApp)
import Typing.Types (Constraint, Kind (..), QualifiedType (..), TyVar (..), Type (..), splitFunctionType)

data LowerState = LowerState
    { lsCounter :: Int
    , lsConstructors :: Map.Map Name MetallicConstructorMetadata
    , lsModuleName :: String
    , lsSymbolEnv :: Map.Map Symbol QualifiedType
    }
    deriving (Show)

newtype LowerM a = LowerM (State LowerState a)
    deriving (Functor, Applicative, Monad, MonadState LowerState)

runLower :: Int -> String -> Map.Map Name MetallicConstructorMetadata -> Map.Map Symbol QualifiedType -> LowerM a -> a
runLower initialCounter modName ctors symEnv (LowerM m) =
    let state' = LowerState initialCounter ctors modName symEnv
    in evalState m state'

lookupConstructor :: Name -> LowerM (Maybe MetallicConstructorMetadata)
lookupConstructor name = gets (Map.lookup name . lsConstructors)

lookupSymbolByName :: String -> LowerM (Maybe Symbol)
lookupSymbolByName name = do
    symEnv <- gets lsSymbolEnv
    pure $ case [sym | sym <- Map.keys symEnv, resolvedSymbolName sym == name] of
        (sym : _) -> Just sym
        [] -> Nothing

lookupConstructorSymbol :: String -> String -> LowerM (Maybe Symbol)
lookupConstructorSymbol ctorName parentTypeName = do
    symEnv <- gets lsSymbolEnv
    pure $ case [ sym
                | sym <- Map.keys symEnv
                , resolvedSymbolName sym == ctorName
                , resolvedSymbolKind sym == DataConstructorSymbol parentTypeName
                ] of
        (sym : _) -> Just sym
        [] -> Nothing

symbolToName :: Symbol -> Name
symbolToName sym = case resolvedSymbolUnique sym of
    Just unique -> NUser unique
    Nothing ->
        error $ "symbolToName: Symbol without Unique: " ++ resolvedSymbolName sym

freshLocalName :: String -> LowerM Name
freshLocalName baseName = do
    n <- gets lsCounter
    modName <- gets lsModuleName
    modify $ \s -> s{lsCounter = n + 1}
    let unique = Unique n modName baseName
    pure $ NUser unique

unresolvedName :: String -> LowerM Name
unresolvedName name = do
    mSymbol <- lookupSymbolByName name
    case mSymbol of
        Just symbol -> pure $ symbolToName symbol
        Nothing -> do
            -- Placeholder name for unresolved variables, the resolver already reported the error
            n <- gets lsCounter
            modName <- gets lsModuleName
            modify $ \s -> s{lsCounter = n + 1}
            let unique = Unique n modName ("$unresolved_" ++ name)
            pure $ NUser unique

collectLocalSymbols :: Expr -> Map.Map String Symbol
collectLocalSymbols = go
  where
    go expr = case expr of
        ExprVar sym _ -> Map.singleton (resolvedSymbolName sym) sym
        ExprApp f a -> go f `Map.union` go a
        ExprLambda _ body _ -> go body
        ExprLet _ value body _ -> go value `Map.union` go body
        ExprIf cond t e _ -> go cond `Map.union` go t `Map.union` go e
        ExprBlock es _ -> Map.unions (map go es)
        ExprArray es _ -> Map.unions (map go es)
        ExprTuple es _ -> Map.unions (map go es)
        ExprPatternMatch scrut arms _ -> go scrut `Map.union` Map.unions (map go arms)
        ExprDerivedPatternMatch arms -> Map.unions (map go arms)
        ExprPatternMatchArm _ body _ -> go body
        ExprCompose stmts _ ->
            Map.unions [go e | CSExpr e _ <- stmts]
                `Map.union` Map.unions [go e | CSBind _ e _ <- stmts]
                `Map.union` Map.unions [go e | CSLet _ e _ <- stmts]
        _ -> Map.empty

lookupLocalSymbol :: Map.Map String Symbol -> String -> LowerM Name
lookupLocalSymbol localSyms name =
    case Map.lookup name localSyms of
        Just sym -> pure $ symbolToName sym
        Nothing -> freshLocalName name

collectComposeSymbols :: [ComposeStmt] -> Map.Map String Symbol
collectComposeSymbols stmts = Map.unions $ map go stmts
  where
    go (CSExpr e _) = collectLocalSymbols e
    go (CSBind _ e _) = collectLocalSymbols e
    go (CSLet _ e _) = collectLocalSymbols e

resolvePattern :: Map.Map String Symbol -> ParsedPattern -> LowerM ResolvedPattern
resolvePattern localSyms (PVar name span') = do
    resolvedName <- lookupLocalSymbol localSyms name
    pure $ PVar resolvedName span'
resolvePattern _ (PWildcard span') = pure $ PWildcard span'
resolvePattern _ (PLit lit span') = pure $ PLit lit span'
resolvePattern localSyms (PConstructor ctorName pats span') = do
    ctors <- gets lsConstructors
    let resolvedCtorName = case findConstructorByString ctorName ctors of
            Just name -> name
            Nothing -> error $ "resolvePattern: Unknown constructor: " ++ ctorName
    resolvedPats <- mapM (resolvePattern localSyms) pats
    pure $ PConstructor resolvedCtorName resolvedPats span'
resolvePattern localSyms (PTuple pats span') = do
    resolvedPats <- mapM (resolvePattern localSyms) pats
    pure $ PTuple resolvedPats span'
resolvePattern localSyms (PArray pats span') = do
    resolvedPats <- mapM (resolvePattern localSyms) pats
    pure $ PArray resolvedPats span'
resolvePattern localSyms (PCons headPat tailPat span') = do
    resolvedHead <- resolvePattern localSyms headPat
    resolvedTail <- resolvePattern localSyms tailPat
    pure $ PCons resolvedHead resolvedTail span'
resolvePattern localSyms (PAs name pat span') = do
    resolvedName <- lookupLocalSymbol localSyms name
    resolvedPat <- resolvePattern localSyms pat
    pure $ PAs resolvedName resolvedPat span'

findConstructorByString :: String -> Map.Map Name MetallicConstructorMetadata -> Maybe Name
findConstructorByString str ctors =
    case [n | n <- Map.keys ctors, nameMatches n str] of
        (n : _) -> Just n
        [] -> Nothing
  where
    nameMatches (NUser u) s = uniqueOriginal u == s
    nameMatches _ _ = False

data LowerResult = LowerResult
    { lrBindings :: [(Name, UntypedExpr, [Type], Type, [TyVar], [Constraint], FunctionAttributes)]
    , lrTypes :: [MetallicTypeDef]
    , lrInstances :: [(QualifiedType, [(Name, UntypedExpr, [Type], Type)])]
    , lrTypeClasses :: [MetallicTypeClassMetadata]
    }
    deriving (Show)

lowerModule :: Expr -> LowerM LowerResult
lowerModule (ExprRoot children) = do
    types <- lowerTypes children
    typeClasses <- lowerTypeClasses children
    bindings <- lowerBindings children
    instances <- lowerInstances children

    pure
        LowerResult
            { lrBindings = bindings
            , lrTypes = types
            , lrInstances = instances
            , lrTypeClasses = typeClasses
            }
lowerModule expr = do
    body <- lowerExpr expr
    mainName <- freshLocalName "main"
    pure
        LowerResult
            { lrBindings = [(mainName, body, [], TUnresolved "infer", [], [], defaultFunctionAttributes)]
            , lrTypes = []
            , lrInstances = []
            , lrTypeClasses = []
            }

lowerTypes :: [Expr] -> LowerM [MetallicTypeDef]
lowerTypes exprs = do
    dataTypes <- mapM lowerType [e | e@ExprDataTypeDef{} <- exprs]
    structs <- mapM lowerStruct [e | e@ExprStructDef{} <- exprs]
    pure $ dataTypes ++ structs

lowerType :: Expr -> LowerM MetallicTypeDef
lowerType (ExprDataTypeDef name _generics _constraints constructors _attrs _span) = do
    typeName <- do
        mSymbol <- lookupSymbolByName name
        case mSymbol of
            Just symbol -> pure $ symbolToName symbol
            Nothing -> freshLocalName name -- Fallback for local types
    ctors <- zipWithM (lowerConstructor name) [0 ..] constructors
    pure $ MAlgebraicType typeName ctors
  where
    lowerConstructor :: String -> Int -> Expr -> LowerM MetallicConstructor
    lowerConstructor parentTypeName tag (ExprDataConstructor ctorName fields _) = do
        ctorNameN <- do
            mSymbol <- lookupConstructorSymbol ctorName parentTypeName
            case mSymbol of
                Just symbol -> pure $ symbolToName symbol
                Nothing -> freshLocalName ctorName -- Fallback
        let fieldTypes = map (lValue . snd) fields
        pure $ MetallicConstructor ctorNameN tag fieldTypes
    lowerConstructor _ _ e = error $ "Expected data constructor, got: " ++ show e
lowerType e = error $ "Expected data type definition, got: " ++ show e

lowerStruct :: Expr -> LowerM MetallicTypeDef
lowerStruct (ExprStructDef name _generics _constraints ctorName fields _attrs _span) = do
    typeName <- do
        mSymbol <- lookupSymbolByName name
        case mSymbol of
            Just symbol -> pure $ symbolToName symbol
            Nothing -> freshLocalName name
    ctorNameN <- do
        mSymbol <- lookupConstructorSymbol ctorName name
        case mSymbol of
            Just symbol -> pure $ symbolToName symbol
            Nothing -> freshLocalName ctorName
    let fieldTypes = map (lValue . snd) fields
    pure $ MStructType typeName ctorNameN fieldTypes
lowerStruct e = error $ "Expected struct definition, got: " ++ show e

lowerTypeClasses :: [Expr] -> LowerM [MetallicTypeClassMetadata]
lowerTypeClasses exprs = mapM lowerTypeClass [e | e@ExprTypeClassDef{} <- exprs]

lowerTypeClass :: Expr -> LowerM MetallicTypeClassMetadata
lowerTypeClass (ExprTypeClassDef className _ methods _) = do
    classNameN <- freshLocalName className
    methodBindings <- mapM extractMethodBinding methods
    pure
        MetallicTypeClassMetadata
            { mtcName = classNameN
            , mtcMethods = methodBindings
            }
  where
    extractMethodBinding :: Expr -> LowerM (Name, QualifiedType)
    extractMethodBinding (ExprTypeClassBinding name (Located _ ty) _ _) = do
        -- Look up the symbol to get the original Unique instead of creating a fresh one
        methodName <- do
            mSymbol <- lookupSymbolByName name
            case mSymbol of
                Just symbol -> pure $ symbolToName symbol
                Nothing -> freshLocalName name -- Fallback for local bindings
        pure (methodName, ty)
    extractMethodBinding e = error $ "Expected type class binding, got: " ++ show e
lowerTypeClass e = error $ "Expected type class definition, got: " ++ show e

lowerBindings :: [Expr] -> LowerM [(Name, UntypedExpr, [Type], Type, [TyVar], [Constraint], FunctionAttributes)]
lowerBindings exprs = mapM lowerBinding [e | e@ExprBindingDef{} <- exprs]

lowerBinding :: Expr -> LowerM (Name, UntypedExpr, [Type], Type, [TyVar], [Constraint], FunctionAttributes)
lowerBinding (ExprBindingDef name (Located _ (Forall typeVars constraints bindingType)) body _isTopLevel attrs _span) = do
    bindingName <- do
        mSymbol <- lookupSymbolByName name
        case mSymbol of
            Just symbol -> pure $ symbolToName symbol
            Nothing -> freshLocalName name -- Fallback for local bindings
    let funcAttrs = attributesToFunctionAttrs (map lValue attrs)
    (paramTypes, returnType, metalBody) <- lowerBindingBody bindingType body
    pure (bindingName, metalBody, paramTypes, returnType, typeVars, constraints, funcAttrs)
lowerBinding e = error $ "Expected binding definition, got: " ++ show e

attributesToFunctionAttrs :: [Attribute] -> FunctionAttributes
attributesToFunctionAttrs = foldr apply defaultFunctionAttributes
  where
    apply AttrInline fa = fa{faInline = True}
    apply AttrNoInline fa = fa{faNoInline = True}
    apply (AttrDeprecated msg) fa = fa{faDeprecated = msg}
    apply (AttrExtern n) fa = fa{faExtern = Just n}

lowerBindingBody :: Type -> Expr -> LowerM ([Type], Type, UntypedExpr)
lowerBindingBody bindingType body = case body of
    ExprLambda paramNames innerBody span' -> do
        let localSyms = collectLocalSymbols innerBody
        let (paramTypes, returnType) = splitFunctionType (length paramNames) bindingType
        metalBody <- lowerExpr innerBody
        paramNamesN <- mapM (lookupLocalSymbol localSyms) paramNames
        pure (paramTypes, returnType, MLambda paramNamesN metalBody () span')
    ExprDerivedPatternMatch arms -> do
        let arity = patternMatchArity body
            (paramTypes, returnType) = splitFunctionType arity bindingType
        paramNames <- mapM (\i -> freshLocalName ("arg" ++ show i)) [0 .. arity - 1]
        let span' = case arms of
                (ExprPatternMatchArm _ _ s : _) -> s
                _ -> dummySpan
        metalArms <- mapM lowerArm arms
        let scrutinees = [MVar pn () span' | pn <- paramNames]
            caseExpr = MCase scrutinees metalArms Nothing () span'
        pure (paramTypes, returnType, MLambda paramNames caseExpr () span')
    _ -> do
        metalBody <- lowerExpr body
        pure ([], bindingType, metalBody)

lowerInstances :: [Expr] -> LowerM [(QualifiedType, [(Name, UntypedExpr, [Type], Type)])]
lowerInstances exprs = mapM lowerInstance [e | e@ExprInstanceDef{} <- exprs]

lowerInstance :: Expr -> LowerM (QualifiedType, [(Name, UntypedExpr, [Type], Type)])
lowerInstance (ExprInstanceDef constraintType methods _) = do
    methodBindings <- mapM lowerInstanceMethod methods
    pure (constraintType, methodBindings)
  where
    lowerInstanceMethod :: Expr -> LowerM (Name, UntypedExpr, [Type], Type)
    lowerInstanceMethod (ExprBindingDef name (Located _ (Forall _ _ methodType)) body _ _ _) = do
        methodName <- do
            mSymbol <- lookupSymbolByName name
            case mSymbol of
                Just symbol -> pure $ symbolToName symbol
                Nothing -> freshLocalName name -- Fallback for local bindings
        (paramTypes, returnType, metalBody) <- lowerBindingBody methodType body
        pure (methodName, metalBody, paramTypes, returnType)
    lowerInstanceMethod e = error $ "Expected binding in instance, got: " ++ show e
lowerInstance e = error $ "Expected instance definition, got: " ++ show e

patternMatchArity :: Expr -> Int
patternMatchArity (ExprDerivedPatternMatch (ExprPatternMatchArm pats _ _ : _)) = length pats
patternMatchArity _ = 0

lowerExpr :: Expr -> LowerM UntypedExpr
lowerExpr expr = case expr of
    ExprNum n span' ->
        pure $ MLit (MInt (read n)) span'
    ExprStr s span' ->
        pure $ MLit (MString s) span'
    ExprBool b span' ->
        pure $ MLit (MBool b) span'
    ExprVar symbol span' -> do
        let name = symbolToName symbol
        case resolvedSymbolKind symbol of
            DataConstructorSymbol _ -> do
                mMeta <- lookupConstructor name
                case mMeta of
                    Just meta ->
                        pure $ MConstruct name (mcmTag meta) [] () span'
                    Nothing ->
                        pure $ MVar name () span'
            BindingSymbol _ ->
                pure $ MCall (MVar name () span') [] () span'
            _ ->
                pure $ MVar name () span'
    ExprUVar name span' -> do
        varName <- unresolvedName name
        pure $ MVar varName () span'
    ExprApp _ _ -> do
        let (base, args) = uncurryApp expr
        lowerApp base args
    ExprLambda params body span' -> do
        let localSyms = collectLocalSymbols body
        paramNames <- mapM (lookupLocalSymbol localSyms) params
        metalBody <- lowerExpr body
        pure $ MLambda paramNames metalBody () span'
    ExprLet{letName, letValue, letBody, letSpan} -> do
        -- Collect local symbols from the body to find the resolved let name
        let localSyms = collectLocalSymbols letBody
        metalValue <- lowerExpr letValue
        metalBody <- lowerExpr letBody
        letNameN <- lookupLocalSymbol localSyms letName
        pure $ MLet letNameN metalValue metalBody () letSpan
    ExprIf{ifCondition, ifBody, ifElseBody, ifSpan} -> do
        metalCond <- lowerExpr ifCondition
        metalThen <- lowerExpr ifBody
        metalElse <- lowerExpr ifElseBody
        pure $ MIf metalCond metalThen metalElse () ifSpan
    ExprArray elements span' -> do
        metalElems <- mapM lowerExpr elements
        pure $ MArrayLit metalElems () span'
    ExprTuple elements span' -> do
        metalElems <- mapM lowerExpr elements
        pure $ MTuple metalElems () span'
    ExprPatternMatch scrutinee arms span' -> do
        metalScrutinee <- lowerExpr scrutinee
        metalArms <- mapM lowerArm arms
        pure $ MCase [metalScrutinee] metalArms Nothing () span'
    ExprDerivedPatternMatch arms -> do
        metalArms <- mapM lowerArm arms
        let span' = case arms of
                (ExprPatternMatchArm _ _ s : _) -> s
                _ -> dummySpan
        pure $ MCase [] metalArms Nothing () span'
    ExprCompose stmts span' ->
        lowerCompose stmts span'
    ExprBindingDef{bindingBody} ->
        lowerExpr bindingBody
    ExprBlock exprs span' -> case exprs of
        [] -> pure $ MTuple [] () span'
        [e] -> lowerExpr e
        _ -> lowerBlock exprs span'
    -- Top-level definitions produce unit tuples since they're handled at module level
    ExprImport{} ->
        pure $ MTuple [] () dummySpan
    ExprExport{} ->
        pure $ MTuple [] () dummySpan
    ExprRoot children -> do
        metalExprs <- mapM lowerExpr [b | b@ExprBindingDef{} <- children]
        case metalExprs of
            [] -> pure $ MTuple [] () dummySpan
            [e] -> pure e
            _ -> pure $ MTuple [] () dummySpan
    ExprDataConstructor{} ->
        pure $ MTuple [] () dummySpan
    ExprTypeClassBinding{} ->
        pure $ MTuple [] () dummySpan
    ExprDataTypeDef{} ->
        pure $ MTuple [] () dummySpan
    ExprStructDef{} ->
        pure $ MTuple [] () dummySpan
    ExprTypeClassDef{} ->
        pure $ MTuple [] () dummySpan
    ExprInstanceDef{} ->
        pure $ MTuple [] () dummySpan
    ExprIntrinsicDef{} ->
        pure $ MTuple [] () dummySpan
    ExprIntrinsicDataTypeDef{} ->
        pure $ MTuple [] () dummySpan
    ExprIntrinsicInstanceDef{} ->
        pure $ MTuple [] () dummySpan
    ExprPatternMatchArm{} ->
        pure $ MTuple [] () dummySpan

lowerArm :: Expr -> LowerM UntypedArm
lowerArm (ExprPatternMatchArm pats body _) = do
    let patSyms = collectPatternSymbols pats
        bodySyms = collectLocalSymbols body
        localSyms = patSyms `Map.union` bodySyms
    resolvedPats <- mapM (resolvePattern localSyms) pats
    metalBody <- lowerExpr body
    pure $ MCaseArm resolvedPats metalBody
lowerArm other = error $ "Invalid pattern match arm: " ++ show other

collectPatternSymbols :: [ParsedPattern] -> Map.Map String Symbol
collectPatternSymbols = Map.unions . map collectPatternSymbol

collectPatternSymbol :: ParsedPattern -> Map.Map String Symbol
collectPatternSymbol pat = case pat of
    PVar {} -> Map.empty -- PVar has String name, not Symbol - will be resolved later
    PWildcard _ -> Map.empty
    PLit {} -> Map.empty
    PConstructor _ pats _ -> collectPatternSymbols pats
    PTuple pats _ -> collectPatternSymbols pats
    PArray pats _ -> collectPatternSymbols pats
    PCons h t _ -> collectPatternSymbol h `Map.union` collectPatternSymbol t
    PAs _ pat' _ -> collectPatternSymbol pat'

lowerApp :: Expr -> [Expr] -> LowerM UntypedExpr
lowerApp base args = do
    let span' = case (base, args) of
            (_, []) -> exprSpan base
            (_, _) ->
                let s1 = exprSpan base
                    s2 = exprSpan (last args)
                in spanBetween s1 s2

    metalArgs <- mapM lowerExpr args

    case base of
        ExprVar symbol _ -> do
            let name = symbolToName symbol
            case resolvedSymbolKind symbol of
                DataConstructorSymbol _ -> do
                    mMeta <- lookupConstructor name
                    case mMeta of
                        Just meta ->
                            pure $ MConstruct name (mcmTag meta) metalArgs () span'
                        Nothing ->
                            pure $ MCall (MVar name () span') metalArgs () span'
                _ ->
                    pure $ MCall (MVar name () span') metalArgs () span'
        _ -> do
            metalBase <- lowerExpr base
            pure $ MCall metalBase metalArgs () span'

lowerCompose :: [ComposeStmt] -> Span -> LowerM UntypedExpr
lowerCompose [] span' = pure $ MTuple [] () span'
lowerCompose [CSExpr e _] _ = lowerExpr e
lowerCompose (stmt : rest) span' = case stmt of
    CSBind name action stmtSpan -> do
        let restSyms = collectComposeSymbols rest
        metalAction <- lowerExpr action
        restExpr <- lowerCompose rest span'

        nameN <- lookupLocalSymbol restSyms name
        let lambda = MLambda [nameN] restExpr () stmtSpan
        bindVarName <- unresolvedName ">>="
        let bindVar = MVar bindVarName () stmtSpan
        pure $ MCall bindVar [metalAction, lambda] () span'
    CSLet name value stmtSpan -> do
        let restSyms = collectComposeSymbols rest
        metalValue <- lowerExpr value
        restExpr <- lowerCompose rest span'
        nameN <- lookupLocalSymbol restSyms name
        pure $ MLet nameN metalValue restExpr () stmtSpan
    CSExpr action stmtSpan -> do
        metalAction <- lowerExpr action
        restExpr <- lowerCompose rest span'

        thenVarName <- unresolvedName ">>"
        let thenVar = MVar thenVarName () stmtSpan
        pure $ MCall thenVar [metalAction, restExpr] () span'

lowerBlock :: [Expr] -> Span -> LowerM UntypedExpr
lowerBlock [] span' = pure $ MTuple [] () span'
lowerBlock [e] _ = lowerExpr e
lowerBlock (e : es) span' = do
    metalE <- lowerExpr e
    metalRest <- lowerBlock es span'
    ignoreName <- freshLocalName "_"
    pure $ MLet ignoreName metalE metalRest () span'

untypedToInference :: Int -> UntypedExpr -> (InferenceExpr, Int)
untypedToInference counter expr = runState (go expr) counter
  where
    freshHole :: State Int TypeSlot
    freshHole = do
        n <- get
        put (n + 1)
        pure $ Hole (TypeVar ("$h" ++ show n) KindStar)

    go :: UntypedExpr -> State Int InferenceExpr
    go (MVar name () span') = do
        hole <- freshHole
        pure $ MVar name hole span'
    go (MLit lit span') = pure $ MLit lit span'
    go (MCall callee args () span') = do
        callee' <- go callee
        args' <- mapM go args
        hole <- freshHole
        pure $ MCall callee' args' hole span'
    go (MTypeApp e tys () span') = do
        e' <- go e
        hole <- freshHole
        pure $ MTypeApp e' tys hole span'
    go (MLet name val body () span') = do
        val' <- go val
        body' <- go body
        hole <- freshHole
        pure $ MLet name val' body' hole span'
    go (MLambda params body () span') = do
        paramHoles <- mapM (const freshHole) params
        body' <- go body
        hole <- freshHole
        pure $ MLambda (zip params paramHoles) body' hole span'
    go (MClosure name captures () span') = do
        captureHoles <- mapM (const freshHole) captures
        hole <- freshHole
        pure $ MClosure name (zip captures captureHoles) hole span'
    go (MConstruct name tag args () span') = do
        args' <- mapM go args
        hole <- freshHole
        pure $ MConstruct name tag args' hole span'
    go (MArrayLit elems () span') = do
        elems' <- mapM go elems
        hole <- freshHole
        pure $ MArrayLit elems' hole span'
    go (MTuple elems () span') = do
        elems' <- mapM go elems
        hole <- freshHole
        pure $ MTuple elems' hole span'
    go (MIf cond thenE elseE () span') = do
        cond' <- go cond
        thenE' <- go thenE
        elseE' <- go elseE
        hole <- freshHole
        pure $ MIf cond' thenE' elseE' hole span'
    go (MCase scruts arms mdef () span') = do
        scruts' <- mapM go scruts
        arms' <- mapM goArm arms
        mdef' <- traverse go mdef
        hole <- freshHole
        pure $ MCase scruts' arms' mdef' hole span'
    go (MFieldAccess e idx () span') = do
        e' <- go e
        hole <- freshHole
        pure $ MFieldAccess e' idx hole span'
    go (MPanic msg () span') = do
        hole <- freshHole
        pure $ MPanic msg hole span'

    goArm :: UntypedArm -> State Int InferenceArm
    goArm (MCaseArm pats body) = do
        body' <- go body
        pure $ MCaseArm pats body'
