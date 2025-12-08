{-# LANGUAGE NamedFieldPuns #-}

module Metal.Lift (
    liftLambdas,
    collectBinders,
    collectBindersTyped,
) where

import Control.Monad.State.Strict
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lexing.Position (dummySpan)
import Metal.Expr
import Metal.Function
import Metal.Metadata (ClosureFunctionInfo (..), MetallicFunctionMetadata (MetallicFunctionMetadata), defaultFunctionAttributes)
import Metal.Module
import Project.Name (LocalId (..), LocalPrefix (..), Name (..))
import Project.Unique (Unique (..))
import Syntax.Patterns (Pattern (..), ResolvedPattern)
import Typing.Types

data ClosureInfo = ClosureInfo
    { ciLiftedName :: Name
    , ciCapturedVars :: [(Name, Type)]
    }
    deriving (Show, Eq)

type LiftM = State LiftState

data LiftState = LiftState
    { lsNextLambdaId :: Int
    , lsLiftedFunctions :: [MetallicFunction]
    , lsGlobalNames :: Set.Set Name
    , lsClosures :: Map.Map Name ClosureInfo
    , lsModuleName :: String
    }

mkLiftState :: Int -> String -> Set.Set Name -> LiftState
mkLiftState startCounter modName globals =
    LiftState
        { lsNextLambdaId = startCounter
        , lsLiftedFunctions = []
        , lsGlobalNames = globals
        , lsClosures = Map.empty
        , lsModuleName = modName
        }

liftLambdas :: Int -> Set.Set Name -> MetallicModule -> MetallicModule
liftLambdas startCounter extraGlobals m@MetallicModule{mmName, mmFunctions, mmInstances} =
    let
        instanceMethodNames = [mfName mf | inst <- mmInstances, mf <- miMethods inst]
        globalNames = Set.union extraGlobals (Set.fromList (map mfName mmFunctions ++ instanceMethodNames))
        (fns', st1) = runState (mapM liftFunctionLambdas mmFunctions) (mkLiftState startCounter mmName globalNames)
        (instances', st2) = runState (mapM liftInstanceLambdas mmInstances) st1
        allFns = fns' ++ lsLiftedFunctions st2
    in
        m{mmFunctions = allFns, mmInstances = instances'}

liftInstanceLambdas :: MetallicInstance -> LiftM MetallicInstance
liftInstanceLambdas inst@MetallicInstance{miMethods} = do
    methods' <- mapM liftFunctionLambdas miMethods
    pure inst{miMethods = methods'}

liftFunctionLambdas :: MetallicFunction -> LiftM MetallicFunction
liftFunctionLambdas fn@MetallicFunction{mfParams, mfBody} = do
    let paramNames = Set.fromList (map fst mfParams)
    let unwrappedBody = unwrapRedundantLambda mfParams mfBody
    body' <- liftExprLambdas paramNames Set.empty unwrappedBody
    pure fn{mfBody = body'}

unwrapRedundantLambda :: [(Name, Type)] -> TypedExpr -> TypedExpr
unwrapRedundantLambda funcParams (MLambda lambdaParams innerBody _ _)
    | length funcParams == length lambdaParams =
        let substitution = Map.fromList $ zip (map fst lambdaParams) (map fst funcParams)
        in substituteVars substitution innerBody
unwrapRedundantLambda _ body = body

substituteVars :: Map.Map Name Name -> TypedExpr -> TypedExpr
substituteVars subst expr = case expr of
    MVar name ty s ->
        case Map.lookup name subst of
            Just newName -> MVar newName ty s
            Nothing -> expr
    MLit{} -> expr
    MCall callee args ty s ->
        MCall (substituteVars subst callee) (map (substituteVars subst) args) ty s
    MTypeApp e tys ty s ->
        MTypeApp (substituteVars subst e) tys ty s
    MLet name val body ty s ->
        let subst' = Map.delete name subst
        in MLet name (substituteVars subst val) (substituteVars subst' body) ty s
    MLambda params body ty s ->
        let subst' = foldr (Map.delete . fst) subst params
        in MLambda params (substituteVars subst' body) ty s
    MConstruct name tag args ty s ->
        MConstruct name tag (map (substituteVars subst) args) ty s
    MArrayLit elems ty s ->
        MArrayLit (map (substituteVars subst) elems) ty s
    MTuple elems ty s ->
        MTuple (map (substituteVars subst) elems) ty s
    MCase scrutinees arms mdef ty s ->
        MCase
            (map (substituteVars subst) scrutinees)
            (map (substituteArm subst) arms)
            (fmap (substituteVars subst) mdef)
            ty
            s
    MIf cond ifB elseB ty s ->
        MIf (substituteVars subst cond) (substituteVars subst ifB) (substituteVars subst elseB) ty s
    MFieldAccess e idx ty s ->
        MFieldAccess (substituteVars subst e) idx ty s
    MPanic{} -> expr
    MClosure name capturedVars ty s ->
        let capturedVars' = [(Map.findWithDefault n n subst, t) | (n, t) <- capturedVars]
        in MClosure name capturedVars' ty s
  where
    substituteArm subst' arm@MCaseArm{mcaPatterns, mcaBody} =
        let boundNames = concatMap collectBindersTyped mcaPatterns
            subst'' = foldr Map.delete subst' boundNames
        in arm{mcaBody = substituteVars subst'' mcaBody}

liftExprLambdas :: Set.Set Name -> Set.Set Name -> TypedExpr -> LiftM TypedExpr
liftExprLambdas _ _ e@(MVar{}) = pure e
liftExprLambdas _ _ e@(MLit _ _) = pure e
liftExprLambdas available bound (MCall callee args ty s) = do
    args' <- mapM (liftExprLambdas available bound) args
    case callee of
        MVar varName _ varSpan -> do
            closures <- gets lsClosures
            case Map.lookup varName closures of
                Just (ClosureInfo liftedName _capturedVars) -> do
                    -- Uniform calling convention: pass closure as first arg
                    -- The lifted function will extract env values from closure_self
                    let closureArg = MVar varName closurePtrType varSpan
                        allArgs = closureArg : args'
                        -- Function type: ClosurePtr -> original params -> return
                        liftedFnType = foldr TArrow ty (closurePtrType : map getType args')
                    pure $ MCall (MVar liftedName liftedFnType varSpan) allArgs ty s
                Nothing -> do
                    callee' <- liftExprLambdas available bound callee
                    pure $ MCall callee' args' ty s
        MLambda params body lambdaTy lambdaSpan -> do
            globals <- gets lsGlobalNames
            let paramSet = Set.fromList (map fst params)
                freeVarsWithTypes = computeFreeVarsWithTypes body
                freeVarsList =
                    [ (n, varTy)
                    | (n, varTy) <- Map.toList freeVarsWithTypes
                    , not (Set.member n paramSet)
                    , not (Set.member n bound)
                    , not (Set.member n globals)
                    ]

            let newAvailable = Set.union paramSet (Set.union available bound)
            body' <- liftExprLambdas newAvailable Set.empty body

            liftedName <- freshLambdaName

            -- Use splitFunctionType with actual param count, not full uncurrying
            let (paramTypes, retType) = splitFunctionType (length params) lambdaTy
                originalParams = zip (map fst params) paramTypes
                -- Uniform calling convention: closure_self is first param
                -- Captured vars are extracted from closure_self by the lowering phase
                liftedParams = (closureSelfName, closurePtrType) : originalParams
                liftedFn =
                    MetallicFunction
                        { mfName = liftedName
                        , mfParams = liftedParams
                        , mfReturnType = retType
                        , mfBody = body'
                        , mfMetadata = MetallicFunctionMetadata [] [] Nothing (Just (ClosureFunctionInfo freeVarsList)) defaultFunctionAttributes
                        }

            addLiftedFunction liftedFn

            -- Immediately applied lambda: allocate closure and call
            let closureExpr = MClosure liftedName freeVarsList lambdaTy lambdaSpan
            -- Create a temporary for the closure and call with it
            -- For immediate application, we generate: let tmp = closure in call(tmp, args)
            tmpName <- freshTmpName
            let closureArg = MVar tmpName closurePtrType dummySpan
                allArgs = closureArg : args'
                fullType = foldr TArrow retType (closurePtrType : map snd originalParams)
                callExpr = MCall (MVar liftedName fullType dummySpan) allArgs ty s
            pure $ MLet tmpName closureExpr callExpr ty s
        _ -> do
            callee' <- liftExprLambdas available bound callee
            pure $ MCall callee' args' ty s
liftExprLambdas available bound (MTypeApp e tys ty s) =
    (\e' -> MTypeApp e' tys ty s) <$> liftExprLambdas available bound e
liftExprLambdas available bound (MLet name val body ty s) = case val of
    MLambda params lambdaBody lambdaTy lambdaSpan -> do
        globals <- gets lsGlobalNames
        let paramSet = Set.fromList (map fst params)
            freeVarsWithTypes = computeFreeVarsWithTypes lambdaBody
            -- For closures, we capture all free variables except:
            -- - lambda's own parameters (paramSet)
            -- - global function names (globals)
            -- Note: we DO capture variables from enclosing scopes (available + bound)
            -- because the closure may escape and outlive the current scope.
            freeVarsList =
                [ (n, varTy)
                | (n, varTy) <- Map.toList freeVarsWithTypes
                , not (Set.member n paramSet)
                , not (Set.member n globals)
                ]

        let newAvailable = Set.union paramSet (Set.union available bound)
        lambdaBody' <- liftExprLambdas newAvailable Set.empty lambdaBody

        liftedName <- freshLambdaName

        let (paramTypes, retType) = splitFunctionType (length params) lambdaTy
            originalParams = zip (map fst params) paramTypes
            liftedParams = (closureSelfName, closurePtrType) : originalParams
            liftedFn =
                MetallicFunction
                    { mfName = liftedName
                    , mfParams = liftedParams
                    , mfReturnType = retType
                    , mfBody = lambdaBody'
                    , mfMetadata = MetallicFunctionMetadata [] [] Nothing (Just (ClosureFunctionInfo freeVarsList)) defaultFunctionAttributes
                    }

        addLiftedFunction liftedFn

        modify $ \st -> st{lsClosures = Map.insert name (ClosureInfo liftedName freeVarsList) (lsClosures st)}

        let closureExpr = MClosure liftedName freeVarsList lambdaTy lambdaSpan
        body' <- liftExprLambdas available (Set.insert name bound) body
        pure $ MLet name closureExpr body' ty s
    _ -> do
        val' <- liftExprLambdas available bound val
        body' <- liftExprLambdas available (Set.insert name bound) body
        pure $ MLet name val' body' ty s
liftExprLambdas available bound (MLambda params body ty s) = do
    globals <- gets lsGlobalNames
    let paramSet = Set.fromList (map fst params)
        freeVarsWithTypes = computeFreeVarsWithTypes body
        -- For closures, we capture all free variables except:
        -- - lambda's own parameters (paramSet)
        -- - global function names (globals)
        freeVarsList =
            [ (name, varTy)
            | (name, varTy) <- Map.toList freeVarsWithTypes
            , not (Set.member name paramSet)
            , not (Set.member name globals)
            ]

    let newAvailable = Set.union paramSet (Set.union available bound)
    body' <- liftExprLambdas newAvailable Set.empty body

    liftedName <- freshLambdaName

    let (paramTypes, retType) = splitFunctionType (length params) ty
        originalParams = zip (map fst params) paramTypes
        liftedParams = (closureSelfName, closurePtrType) : originalParams
        liftedFn =
            MetallicFunction
                { mfName = liftedName
                , mfParams = liftedParams
                , mfReturnType = retType
                , mfBody = body'
                , mfMetadata = MetallicFunctionMetadata [] [] Nothing (Just (ClosureFunctionInfo freeVarsList)) defaultFunctionAttributes
                }

    addLiftedFunction liftedFn

    -- All lambdas become closures
    pure (MClosure liftedName freeVarsList ty s)
liftExprLambdas available bound (MConstruct name tag args ty s) =
    MConstruct name tag <$> mapM (liftExprLambdas available bound) args <*> pure ty <*> pure s
liftExprLambdas available bound (MArrayLit elems ty s) =
    MArrayLit <$> mapM (liftExprLambdas available bound) elems <*> pure ty <*> pure s
liftExprLambdas available bound (MTuple elems ty s) =
    MTuple <$> mapM (liftExprLambdas available bound) elems <*> pure ty <*> pure s
liftExprLambdas available bound (MCase scrutinees arms mdef ty s) =
    MCase
        <$> mapM (liftExprLambdas available bound) scrutinees
        <*> mapM (liftArm available bound) arms
        <*> mapM (liftExprLambdas available bound) mdef
        <*> pure ty
        <*> pure s
  where
    liftArm :: Set.Set Name -> Set.Set Name -> TypedArm -> LiftM TypedArm
    liftArm avail boundVars MCaseArm{mcaPatterns, mcaBody} =
        let binders = concatMap collectBindersTyped mcaPatterns
            boundInArm = Set.union boundVars (Set.fromList binders)
        in MCaseArm mcaPatterns <$> liftExprLambdas avail boundInArm mcaBody
liftExprLambdas available bound (MIf ifCond ifBlock elseBlock ty s) =
    MIf
        <$> liftExprLambdas available bound ifCond
        <*> liftExprLambdas available bound ifBlock
        <*> liftExprLambdas available bound elseBlock
        <*> pure ty
        <*> pure s
liftExprLambdas available bound (MFieldAccess e idx ty s) =
    (\e' -> MFieldAccess e' idx ty s) <$> liftExprLambdas available bound e
liftExprLambdas _ _ e@(MPanic{}) = pure e
-- MClosure is already lifted, just pass through
liftExprLambdas _ _ e@(MClosure{}) = pure e

freshLambdaId :: LiftM Int
freshLambdaId = do
    st <- get
    let i = lsNextLambdaId st
    put st{lsNextLambdaId = i + 1}
    pure i

freshLambdaName :: LiftM Name
freshLambdaName = do
    st <- get
    lambdaId <- freshLambdaId
    let modName = lsModuleName st
    let unique = Unique lambdaId modName ("lambda$" ++ show lambdaId)
    pure $ NUser unique

freshTmpName :: LiftM Name
freshTmpName = do
    st <- get
    lambdaId <- freshLambdaId
    let modName = lsModuleName st
    let unique = Unique lambdaId modName ("closure_tmp$" ++ show lambdaId)
    pure $ NUser unique

{- | Create a Name for closure_self parameter
Uses index 0 since there's only ever one closure_self per lifted function
-}
closureSelfName :: Name
closureSelfName = NLocal (LocalId LPClosureSelf 0)

addLiftedFunction :: MetallicFunction -> LiftM ()
addLiftedFunction fn = modify $ \st ->
    st
        { lsLiftedFunctions = fn : lsLiftedFunctions st
        , lsGlobalNames = Set.insert (mfName fn) (lsGlobalNames st)
        }

computeFreeVarsWithTypes :: TypedExpr -> Map.Map Name Type
computeFreeVarsWithTypes (MVar v t _) = Map.singleton v t
computeFreeVarsWithTypes (MLit _ _) = Map.empty
computeFreeVarsWithTypes (MCall callee args _ _) =
    Map.unions (computeFreeVarsWithTypes callee : map computeFreeVarsWithTypes args)
computeFreeVarsWithTypes (MTypeApp e _ _ _) = computeFreeVarsWithTypes e
computeFreeVarsWithTypes (MLet name val body _ _) =
    Map.union (computeFreeVarsWithTypes val) (Map.delete name (computeFreeVarsWithTypes body))
computeFreeVarsWithTypes (MLambda params body _ _) =
    foldr (Map.delete . fst) (computeFreeVarsWithTypes body) params
computeFreeVarsWithTypes (MConstruct _ _ args _ _) = Map.unions (map computeFreeVarsWithTypes args)
computeFreeVarsWithTypes (MArrayLit elems _ _) = Map.unions (map computeFreeVarsWithTypes elems)
computeFreeVarsWithTypes (MTuple elems _ _) = Map.unions (map computeFreeVarsWithTypes elems)
computeFreeVarsWithTypes (MCase scrutinees arms mdef _ _) =
    let scrFree = Map.unions (map computeFreeVarsWithTypes scrutinees)
        armsFree =
            Map.unions
                [ foldr Map.delete (computeFreeVarsWithTypes (mcaBody arm)) (concatMap collectBindersTyped (mcaPatterns arm))
                | arm <- arms
                ]
        defFree = maybe Map.empty computeFreeVarsWithTypes mdef
    in Map.unions [scrFree, armsFree, defFree]
computeFreeVarsWithTypes (MFieldAccess e _ _ _) = computeFreeVarsWithTypes e
computeFreeVarsWithTypes (MIf cond ifB elseB _ _) =
    Map.unions (map computeFreeVarsWithTypes [cond, ifB, elseB])
computeFreeVarsWithTypes (MPanic{}) = Map.empty
computeFreeVarsWithTypes (MClosure _ capturedVars _ _) =
    Map.fromList capturedVars

collectBinders :: ResolvedPattern -> [Name]
collectBinders (PVar name _) = [name]
collectBinders PWildcard{} = []
collectBinders PLit{} = []
collectBinders (PAs name p _) = name : collectBinders p
collectBinders (PConstructor _ ps _) = concatMap collectBinders ps
collectBinders (PTuple ps _) = concatMap collectBinders ps
collectBinders (PArray ps _) = concatMap collectBinders ps

collectBindersTyped :: TypedPattern -> [Name]
collectBindersTyped (Metal.Expr.TPVar name _ _) = [name]
collectBindersTyped Metal.Expr.TPWildcard{} = []
collectBindersTyped Metal.Expr.TPLit{} = []
collectBindersTyped (Metal.Expr.TPAs name p _ _) = name : collectBindersTyped p
collectBindersTyped (Metal.Expr.TPConstructor _ ps _ _) = concatMap collectBindersTyped ps
collectBindersTyped (Metal.Expr.TPTuple ps _ _) = concatMap collectBindersTyped ps
collectBindersTyped (Metal.Expr.TPArray ps _ _) = concatMap collectBindersTyped ps
