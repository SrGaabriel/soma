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
import Typing.Types (Constraint, Kind (..), QualifiedType (..), TyVar (..), Type (..))

data LowerState = LowerState
    { lsCounter :: Int
    , lsConstructors :: Map.Map Name MetallicConstructorMetadata
    , lsModuleName :: String
    , lsSymbolEnv :: Map.Map Symbol QualifiedType
    }
    deriving (Show)

newtype LowerM a = LowerM (State LowerState a)
    deriving (Functor, Applicative, Monad, MonadState LowerState)

runLower :: String -> Map.Map Name MetallicConstructorMetadata -> Map.Map Symbol QualifiedType -> LowerM a -> a
runLower modName ctors symEnv (LowerM m) =
    let state' = LowerState 0 ctors modName symEnv
    in evalState m state'

freshHole :: Kind -> LowerM TypeSlot
freshHole k = do
    n <- gets lsCounter
    modify $ \s -> s{lsCounter = n + 1}
    pure $ Hole (TypeVar ("$h" ++ show n) k)

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
    { lrBindings :: [(Name, InferenceExpr, [Type], Type, [TyVar], [Constraint], FunctionAttributes)]
    , lrTypes :: [MetallicTypeDef]
    , lrInstances :: [(QualifiedType, [(Name, InferenceExpr, [Type], Type)])]
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
            { lrBindings = [(mainName, body, [], slotToType (inferenceSlot body), [], [], defaultFunctionAttributes)]
            , lrTypes = []
            , lrInstances = []
            , lrTypeClasses = []
            }

lowerTypes :: [Expr] -> LowerM [MetallicTypeDef]
lowerTypes exprs = mapM lowerType [e | e@ExprDataTypeDef{} <- exprs]

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

lowerBindings :: [Expr] -> LowerM [(Name, InferenceExpr, [Type], Type, [TyVar], [Constraint], FunctionAttributes)]
lowerBindings exprs = mapM lowerBinding [e | e@ExprBindingDef{} <- exprs]

lowerBinding :: Expr -> LowerM (Name, InferenceExpr, [Type], Type, [TyVar], [Constraint], FunctionAttributes)
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

lowerBindingBody :: Type -> Expr -> LowerM ([Type], Type, InferenceExpr)
lowerBindingBody bindingType body = case body of
    ExprLambda paramNames innerBody span' -> do
        let localSyms = collectLocalSymbols innerBody
        let (paramTypes, returnType) = splitFunctionType (length paramNames) bindingType
        metalBody <- lowerExpr innerBody
        paramNamesN <- mapM (lookupLocalSymbol localSyms) paramNames
        let typedParams = zip paramNamesN (map Known paramTypes)
        pure (paramTypes, returnType, MLambda typedParams metalBody (Known bindingType) span')
    ExprDerivedPatternMatch arms -> do
        let arity = patternMatchArity body
            (paramTypes, returnType) = splitFunctionType arity bindingType
        paramNames <- mapM (\i -> freshLocalName ("arg" ++ show i)) [0 .. arity - 1]
        let span' = case arms of
                (ExprPatternMatchArm _ _ s : _) -> s
                _ -> dummySpan
        metalArms <- mapM lowerArm arms
        let scrutinees = [MVar pn (Known pt) span' | (pn, pt) <- zip paramNames paramTypes]
            typedParams = zip paramNames (map Known paramTypes)
            caseExpr = MCase scrutinees metalArms Nothing (Known returnType) span'
        pure (paramTypes, returnType, MLambda typedParams caseExpr (Known bindingType) span')
    _ -> do
        metalBody <- lowerExpr body
        pure ([], bindingType, metalBody)

lowerInstances :: [Expr] -> LowerM [(QualifiedType, [(Name, InferenceExpr, [Type], Type)])]
lowerInstances exprs = mapM lowerInstance [e | e@ExprInstanceDef{} <- exprs]

lowerInstance :: Expr -> LowerM (QualifiedType, [(Name, InferenceExpr, [Type], Type)])
lowerInstance (ExprInstanceDef constraintType methods _) = do
    methodBindings <- mapM lowerInstanceMethod methods
    pure (constraintType, methodBindings)
  where
    lowerInstanceMethod :: Expr -> LowerM (Name, InferenceExpr, [Type], Type)
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

splitFunctionType :: Int -> Type -> ([Type], Type)
splitFunctionType 0 ty = ([], ty)
splitFunctionType n (TArrow argTy restTy) =
    let (args, ret) = splitFunctionType (n - 1) restTy
    in (argTy : args, ret)
splitFunctionType _ ty = ([], ty)

patternMatchArity :: Expr -> Int
patternMatchArity (ExprDerivedPatternMatch (ExprPatternMatchArm pats _ _ : _)) = length pats
patternMatchArity _ = 0

lowerExpr :: Expr -> LowerM InferenceExpr
lowerExpr expr = case expr of
    ExprNum n span' ->
        pure $ MLit (MInt (read n)) span'
    ExprStr s span' ->
        pure $ MLit (MString s) span'
    ExprBool b span' ->
        pure $ MLit (MBool b) span'
    ExprVar symbol span' -> do
        hole <- freshHole KindStar
        let name = symbolToName symbol
        case resolvedSymbolKind symbol of
            DataConstructorSymbol _ -> do
                mMeta <- lookupConstructor name
                case mMeta of
                    Just meta ->
                        pure $ MConstruct name (mcmTag meta) [] hole span'
                    Nothing ->
                        pure $ MVar name hole span'
            BindingSymbol _ ->
                pure $ MCall (MVar name hole span') [] hole span'
            _ ->
                pure $ MVar name hole span'
    ExprUVar name span' -> do
        hole <- freshHole KindStar
        varName <- unresolvedName name
        pure $ MVar varName hole span'
    ExprApp _ _ -> do
        let (base, args) = uncurryApp expr
        lowerApp base args
    ExprLambda params body span' -> do
        let localSyms = collectLocalSymbols body
        paramHoles <- mapM (\_ -> freshHole KindStar) params
        paramNames <- mapM (lookupLocalSymbol localSyms) params
        let typedParams = zip paramNames paramHoles
        metalBody <- lowerExpr body
        hole <- freshHole KindStar
        pure $ MLambda typedParams metalBody hole span'
    ExprLet{letName, letValue, letBody, letSpan} -> do
        -- Collect local symbols from the body to find the resolved let name
        let localSyms = collectLocalSymbols letBody
        metalValue <- lowerExpr letValue
        metalBody <- lowerExpr letBody
        hole <- freshHole KindStar
        letNameN <- lookupLocalSymbol localSyms letName
        pure $ MLet letNameN metalValue metalBody hole letSpan
    ExprIf{ifCondition, ifBody, ifElseBody, ifSpan} -> do
        metalCond <- lowerExpr ifCondition
        metalThen <- lowerExpr ifBody
        metalElse <- lowerExpr ifElseBody
        hole <- freshHole KindStar
        pure $ MIf metalCond metalThen metalElse hole ifSpan
    ExprArray elements span' -> do
        metalElems <- mapM lowerExpr elements
        hole <- freshHole KindStar
        pure $ MArrayLit metalElems hole span'
    ExprTuple elements span' -> do
        metalElems <- mapM lowerExpr elements
        hole <- freshHole KindStar
        pure $ MTuple metalElems hole span'
    ExprPatternMatch scrutinee arms span' -> do
        metalScrutinee <- lowerExpr scrutinee
        metalArms <- mapM lowerArm arms
        hole <- freshHole KindStar
        pure $ MCase [metalScrutinee] metalArms Nothing hole span'
    ExprDerivedPatternMatch arms -> do
        metalArms <- mapM lowerArm arms
        hole <- freshHole KindStar
        let span' = case arms of
                (ExprPatternMatchArm _ _ s : _) -> s
                _ -> dummySpan
        pure $ MCase [] metalArms Nothing hole span'
    ExprCompose stmts span' ->
        lowerCompose stmts span'
    ExprBindingDef{bindingBody} ->
        lowerExpr bindingBody
    ExprBlock exprs span' -> case exprs of
        [] -> do
            hole <- freshHole KindStar
            pure $ MTuple [] hole span'
        [e] -> lowerExpr e
        _ -> lowerBlock exprs span'
    -- Top-level definitions produce unit tuples since they're handled at module level
    ExprImport{} -> do
        hole <- freshHole KindStar
        pure $ MTuple [] hole dummySpan
    ExprRoot children -> do
        metalExprs <- mapM lowerExpr [b | b@ExprBindingDef{} <- children]
        hole <- freshHole KindStar
        case metalExprs of
            [] -> pure $ MTuple [] hole dummySpan
            [e] -> pure e
            _ -> pure $ MTuple [] hole dummySpan
    ExprDataConstructor{} -> do
        hole <- freshHole KindStar
        pure $ MTuple [] hole dummySpan
    ExprTypeClassBinding{} -> do
        hole <- freshHole KindStar
        pure $ MTuple [] hole dummySpan
    ExprDataTypeDef{} -> do
        hole <- freshHole KindStar
        pure $ MTuple [] hole dummySpan
    ExprTypeClassDef{} -> do
        hole <- freshHole KindStar
        pure $ MTuple [] hole dummySpan
    ExprInstanceDef{} -> do
        hole <- freshHole KindStar
        pure $ MTuple [] hole dummySpan
    ExprIntrinsicDef{} -> do
        hole <- freshHole KindStar
        pure $ MTuple [] hole dummySpan
    ExprIntrinsicDataTypeDef{} -> do
        hole <- freshHole KindStar
        pure $ MTuple [] hole dummySpan
    ExprIntrinsicInstanceDef{} -> do
        hole <- freshHole KindStar
        pure $ MTuple [] hole dummySpan
    ExprPatternMatchArm{} -> do
        hole <- freshHole KindStar
        pure $ MTuple [] hole dummySpan

lowerArm :: Expr -> LowerM InferenceArm
lowerArm (ExprPatternMatchArm pats body _) = do
    let localSyms = collectLocalSymbols body
    resolvedPats <- mapM (resolvePattern localSyms) pats
    metalBody <- lowerExpr body
    pure $ MCaseArm resolvedPats metalBody
lowerArm other = error $ "Invalid pattern match arm: " ++ show other

lowerApp :: Expr -> [Expr] -> LowerM InferenceExpr
lowerApp base args = do
    let span' = case (base, args) of
            (_, []) -> exprSpan base
            (_, _) ->
                let s1 = exprSpan base
                    s2 = exprSpan (last args)
                in spanBetween s1 s2

    metalArgs <- mapM lowerExpr args
    hole <- freshHole KindStar

    case base of
        ExprVar symbol _ -> do
            let name = symbolToName symbol
            case resolvedSymbolKind symbol of
                DataConstructorSymbol _ -> do
                    mMeta <- lookupConstructor name
                    case mMeta of
                        Just meta ->
                            pure $ MConstruct name (mcmTag meta) metalArgs hole span'
                        Nothing -> do
                            baseHole <- freshHole KindStar
                            pure $ MCall (MVar name baseHole span') metalArgs hole span'
                _ -> do
                    baseHole <- freshHole KindStar
                    pure $ MCall (MVar name baseHole span') metalArgs hole span'
        _ -> do
            metalBase <- lowerExpr base
            pure $ MCall metalBase metalArgs hole span'

lowerCompose :: [ComposeStmt] -> Span -> LowerM InferenceExpr
lowerCompose [] span' = do
    hole <- freshHole KindStar
    pure $ MTuple [] hole span'
lowerCompose [CSExpr e _] _ = lowerExpr e
lowerCompose (stmt : rest) span' = case stmt of
    CSBind name action stmtSpan -> do
        let restSyms = collectComposeSymbols rest
        metalAction <- lowerExpr action
        restExpr <- lowerCompose rest span'

        bindHole <- freshHole KindStar
        lambdaParamHole <- freshHole KindStar
        lambdaHole <- freshHole KindStar
        resultHole <- freshHole KindStar

        nameN <- lookupLocalSymbol restSyms name
        let lambda = MLambda [(nameN, lambdaParamHole)] restExpr lambdaHole stmtSpan
        bindVarName <- unresolvedName ">>="
        let bindVar = MVar bindVarName bindHole stmtSpan
        pure $ MCall bindVar [metalAction, lambda] resultHole span'
    CSLet name value stmtSpan -> do
        let restSyms = collectComposeSymbols rest
        metalValue <- lowerExpr value
        restExpr <- lowerCompose rest span'
        hole <- freshHole KindStar
        nameN <- lookupLocalSymbol restSyms name
        pure $ MLet nameN metalValue restExpr hole stmtSpan
    CSExpr action stmtSpan -> do
        metalAction <- lowerExpr action
        restExpr <- lowerCompose rest span'

        thenHole <- freshHole KindStar
        resultHole <- freshHole KindStar

        thenVarName <- unresolvedName ">>"
        let thenVar = MVar thenVarName thenHole stmtSpan
        pure $ MCall thenVar [metalAction, restExpr] resultHole span'

lowerBlock :: [Expr] -> Span -> LowerM InferenceExpr
lowerBlock [] span' = do
    hole <- freshHole KindStar
    pure $ MTuple [] hole span'
lowerBlock [e] _ = lowerExpr e
lowerBlock (e : es) span' = do
    metalE <- lowerExpr e
    metalRest <- lowerBlock es span'
    hole <- freshHole KindStar
    ignoreName <- freshLocalName "_"
    pure $ MLet ignoreName metalE metalRest hole span'
