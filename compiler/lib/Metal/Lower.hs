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
) where

import Control.Monad (zipWithM)
import Control.Monad.State
import qualified Data.Map as Map
import Lexing.Position (Located (..), Span (..), dummySpan)
import Metal.Expr hiding (exprSpan)
import Metal.Metadata (FunctionAttributes (..), MetallicConstructorMetadata (..), MetallicTypeClassMetadata (..), defaultFunctionAttributes)
import Metal.Module (MetallicConstructor (..), MetallicTypeDef (..))
import Project.Symbols (Symbol (..), SymbolKind (..))
import Syntax.Tree (Attribute (..), ComposeStmt (..), Expr (..), exprSpan, uncurryApp)
import Typing.Types (Constraint, Kind (..), QualifiedType (..), TyConstructor (..), TyVar (..), Type (..))

data LowerState = LowerState
    { lsCounter :: Int
    , lsConstructors :: Map.Map String MetallicConstructorMetadata
    }
    deriving (Show)

newtype LowerM a = LowerM (State LowerState a)
    deriving (Functor, Applicative, Monad, MonadState LowerState)

runLower :: Map.Map String MetallicConstructorMetadata -> LowerM a -> a
runLower ctors (LowerM m) = evalState m (LowerState 0 ctors)

freshHole :: Kind -> LowerM TypeSlot
freshHole k = do
    n <- gets lsCounter
    modify $ \s -> s{lsCounter = n + 1}
    pure $ Hole (TypeVar ("$h" ++ show n) k)

lookupConstructor :: String -> LowerM (Maybe MetallicConstructorMetadata)
lookupConstructor name = gets (Map.lookup name . lsConstructors)

data LowerResult = LowerResult
    { lrBindings :: [(String, InferenceExpr, [Type], Type, [TyVar], [Constraint], FunctionAttributes)]
    , lrTypes :: [MetallicTypeDef]
    , lrInstances :: [(QualifiedType, [(String, InferenceExpr, [Type], Type)])]
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
    pure
        LowerResult
            { lrBindings = [("main", body, [], slotToType (inferenceSlot body), [], [], defaultFunctionAttributes)]
            , lrTypes = []
            , lrInstances = []
            , lrTypeClasses = []
            }

lowerTypes :: [Expr] -> LowerM [MetallicTypeDef]
lowerTypes exprs = mapM lowerType [e | e@ExprDataTypeDef{} <- exprs]

lowerType :: Expr -> LowerM MetallicTypeDef
lowerType (ExprDataTypeDef name _generics _constraints constructors _attrs _span) = do
    ctors <- zipWithM lowerConstructor [0 ..] constructors
    pure $ MAlgebraicType name ctors
  where
    lowerConstructor :: Int -> Expr -> LowerM MetallicConstructor
    lowerConstructor tag (ExprDataConstructor ctorName fields _) = do
        let fieldTypes = map (lValue . snd) fields
        pure $ MetallicConstructor ctorName tag fieldTypes
    lowerConstructor _ e = error $ "Expected data constructor, got: " ++ show e
lowerType e = error $ "Expected data type definition, got: " ++ show e

lowerTypeClasses :: [Expr] -> LowerM [MetallicTypeClassMetadata]
lowerTypeClasses exprs = mapM lowerTypeClass [e | e@ExprTypeClassDef{} <- exprs]

lowerTypeClass :: Expr -> LowerM MetallicTypeClassMetadata
lowerTypeClass (ExprTypeClassDef className _ methods _) = do
    let methodBindings = [(extractMethodName m, extractMethodType m) | m <- methods]
    pure
        MetallicTypeClassMetadata
            { mtcName = className
            , mtcMethods = methodBindings
            }
  where
    extractMethodName (ExprTypeClassBinding name _ _ _) = name
    extractMethodName _ = ""

    extractMethodType (ExprTypeClassBinding _ (Located _ qtype) _ _) = qtype
    extractMethodType _ = Forall [] [] (TConstructor (TypeConstructor "Unknown" KindStar))
lowerTypeClass e = error $ "Expected type class definition, got: " ++ show e

lowerBindings :: [Expr] -> LowerM [(String, InferenceExpr, [Type], Type, [TyVar], [Constraint], FunctionAttributes)]
lowerBindings exprs = mapM lowerBinding [e | e@ExprBindingDef{} <- exprs]

lowerBinding :: Expr -> LowerM (String, InferenceExpr, [Type], Type, [TyVar], [Constraint], FunctionAttributes)
lowerBinding (ExprBindingDef name (Located _ (Forall typeVars constraints bindingType)) body _isTopLevel attrs _span) = do
    let funcAttrs = attributesToFunctionAttrs (map lValue attrs)
    (paramTypes, returnType, metalBody) <- lowerBindingBody bindingType body
    pure (name, metalBody, paramTypes, returnType, typeVars, constraints, funcAttrs)
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
        let (paramTypes, returnType) = splitFunctionType (length paramNames) bindingType
        metalBody <- lowerExpr innerBody
        let typedParams = zip paramNames (map Known paramTypes)
        pure (paramTypes, returnType, MLambda typedParams metalBody (Known bindingType) span')
    ExprDerivedPatternMatch arms -> do
        let arity = patternMatchArity body
            (paramTypes, returnType) = splitFunctionType arity bindingType
            paramNames = ["arg" ++ show i | i <- [0 .. arity - 1]]
            span' = case arms of
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

lowerInstances :: [Expr] -> LowerM [(QualifiedType, [(String, InferenceExpr, [Type], Type)])]
lowerInstances exprs = mapM lowerInstance [e | e@ExprInstanceDef{} <- exprs]

lowerInstance :: Expr -> LowerM (QualifiedType, [(String, InferenceExpr, [Type], Type)])
lowerInstance (ExprInstanceDef constraintType methods _) = do
    methodBindings <- mapM lowerInstanceMethod methods
    pure (constraintType, methodBindings)
  where
    lowerInstanceMethod :: Expr -> LowerM (String, InferenceExpr, [Type], Type)
    lowerInstanceMethod (ExprBindingDef name (Located _ (Forall _ _ methodType)) body _ _ _) = do
        (paramTypes, returnType, metalBody) <- lowerBindingBody methodType body
        pure (name, metalBody, paramTypes, returnType)
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
        let name = resolvedSymbolName symbol
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
        pure $ MVar name hole span'
    ExprApp _ _ -> do
        let (base, args) = uncurryApp expr
        lowerApp base args
    ExprLambda params body span' -> do
        paramHoles <- mapM (\_ -> freshHole KindStar) params
        let typedParams = zip params paramHoles
        metalBody <- lowerExpr body
        hole <- freshHole KindStar
        pure $ MLambda typedParams metalBody hole span'
    ExprLet{letName, letValue, letBody, letSpan} -> do
        metalValue <- lowerExpr letValue
        metalBody <- lowerExpr letBody
        hole <- freshHole KindStar
        pure $ MLet letName metalValue metalBody hole letSpan
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
    ExprPatternMatchArm{} -> do
        hole <- freshHole KindStar
        pure $ MTuple [] hole dummySpan

lowerArm :: Expr -> LowerM InferenceArm
lowerArm (ExprPatternMatchArm pats body _) = do
    metalBody <- lowerExpr body
    pure $ MCaseArm pats metalBody
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
            let name = resolvedSymbolName symbol
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
        metalAction <- lowerExpr action
        restExpr <- lowerCompose rest span'

        bindHole <- freshHole KindStar
        lambdaParamHole <- freshHole KindStar
        lambdaHole <- freshHole KindStar
        resultHole <- freshHole KindStar

        let lambda = MLambda [(name, lambdaParamHole)] restExpr lambdaHole stmtSpan
        let bindVar = MVar ">>=" bindHole stmtSpan
        pure $ MCall bindVar [metalAction, lambda] resultHole span'
    CSLet name value stmtSpan -> do
        metalValue <- lowerExpr value
        restExpr <- lowerCompose rest span'
        hole <- freshHole KindStar
        pure $ MLet name metalValue restExpr hole stmtSpan
    CSExpr action stmtSpan -> do
        metalAction <- lowerExpr action
        restExpr <- lowerCompose rest span'

        thenHole <- freshHole KindStar
        resultHole <- freshHole KindStar

        let thenVar = MVar ">>" thenHole stmtSpan
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
    pure $ MLet "_" metalE metalRest hole span'

-- | Combine two spans into one spanning both
spanBetween :: Span -> Span -> Span
spanBetween (Span s1 _) (Span _ e2) = Span s1 e2
