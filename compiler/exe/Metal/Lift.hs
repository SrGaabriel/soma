{-# LANGUAGE NamedFieldPuns #-}

module Metal.Lift (
    liftLambdas,
    collectBinders,
) where

import Control.Monad.State.Strict
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Metal.Expr
import Metal.Function
import Metal.Metadata
import Metal.Module
import Syntax.Patterns (Pattern (..))
import Typing.Types

data ClosureInfo = ClosureInfo
    { ciLiftedName :: String
    , ciCapturedVars :: [(String, Type)]
    }
    deriving (Show, Eq)

type LiftM = State LiftState

data LiftState = LiftState
    { lsNextLambdaId :: Int
    , lsLiftedFunctions :: [MetallicFunction]
    , lsGlobalNames :: Set.Set String
    , lsClosures :: Map.Map String ClosureInfo
    }

emptyLiftState :: Set.Set String -> LiftState
emptyLiftState globals =
    LiftState
        { lsNextLambdaId = 0
        , lsLiftedFunctions = []
        , lsGlobalNames = globals
        , lsClosures = Map.empty
        }

liftLambdas :: Set.Set String -> MetallicModule -> MetallicModule
liftLambdas extraGlobals m@MetallicModule{mmFunctions} =
    let globalNames = Set.union extraGlobals (Set.fromList (map mfName mmFunctions))
        (fns', st) = runState (mapM liftFunctionLambdas mmFunctions) (emptyLiftState globalNames)
        allFns = fns' ++ lsLiftedFunctions st
    in m{mmFunctions = allFns}

liftFunctionLambdas :: MetallicFunction -> LiftM MetallicFunction
liftFunctionLambdas fn@MetallicFunction{mfParams, mfBody} = do
    let paramNames = Set.fromList (map fst mfParams)
    body' <- liftExprLambdas paramNames Set.empty mfBody
    pure fn{mfBody = body'}

liftExprLambdas :: Set.Set String -> Set.Set String -> MetallicExpr -> LiftM MetallicExpr
liftExprLambdas _ _ e@(MVar _ _) = pure e
liftExprLambdas _ _ e@(MLit _) = pure e
liftExprLambdas available bound (MCall callee args ty) = do
    args' <- mapM (liftExprLambdas available bound) args
    case callee of
        MVar varName _ -> do
            closures <- gets lsClosures
            case Map.lookup varName closures of
                Just (ClosureInfo liftedName _capturedVars) -> do
                    -- Uniform calling convention: pass closure as first arg
                    -- The lifted function will extract env values from closure_self
                    let closureArg = MVar varName closurePtrType
                        allArgs = closureArg : args'
                        -- Function type: ClosurePtr -> original params -> return
                        liftedFnType = foldr TArrow ty (closurePtrType : map getType args')
                    pure $ MCall (MVar liftedName liftedFnType) allArgs ty
                Nothing -> do
                    callee' <- liftExprLambdas available bound callee
                    pure $ MCall callee' args' ty
        MLambda params body lambdaTy -> do
            globals <- gets lsGlobalNames
            let paramSet = Set.fromList params
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

            lambdaId <- freshLambdaId
            let liftedName = "lambda$" ++ show lambdaId

            -- Use splitFunctionType with actual param count, not full uncurrying
            let (paramTypes, retType) = splitFunctionType (length params) lambdaTy
                originalParams = zip params paramTypes
                -- Uniform calling convention: closure_self is first param
                -- Captured vars are extracted from closure_self by the lowering phase
                liftedParams = ("closure_self", closurePtrType) : originalParams
                liftedFn =
                    MetallicFunction
                        { mfName = liftedName
                        , mfParams = liftedParams
                        , mfReturnType = retType
                        , mfBody = body'
                        , mfMetadata =
                            MetallicFunctionMetadata
                                { mfmOriginalName = []
                                , mfmConstraints = []
                                , mfmInstanceInfo = Nothing
                                , mfmClosureInfo = Just (ClosureFunctionInfo freeVarsList)
                                , mfmIsInline = False
                                }
                        }

            addLiftedFunction liftedFn

            -- Immediately applied lambda: allocate closure and call
            let closureExpr = MClosure liftedName freeVarsList lambdaTy
            -- Create a temporary for the closure and call with it
            -- For immediate application, we generate: let tmp = closure in call(tmp, args)
            tmpName <- freshTmpName
            let closureArg = MVar tmpName closurePtrType
                allArgs = closureArg : args'
                fullType = foldr TArrow retType (closurePtrType : map snd originalParams)
                callExpr = MCall (MVar liftedName fullType) allArgs ty
            pure $ MLet tmpName closureExpr callExpr ty
        _ -> do
            callee' <- liftExprLambdas available bound callee
            pure $ MCall callee' args' ty
liftExprLambdas available bound (MTypeApp e tys ty) =
    (\e' -> MTypeApp e' tys ty) <$> liftExprLambdas available bound e
liftExprLambdas available bound (MLet name val body ty) = do
    case val of
        MLambda params lambdaBody lambdaTy -> do
            globals <- gets lsGlobalNames
            let paramSet = Set.fromList params
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

            lambdaId <- freshLambdaId
            let liftedName = "lambda$" ++ show lambdaId

            -- Use splitFunctionType with actual param count, not full uncurrying
            let (paramTypes, retType) = splitFunctionType (length params) lambdaTy
                originalParams = zip params paramTypes
                -- Uniform calling convention: closure_self is first param
                liftedParams = ("closure_self", closurePtrType) : originalParams
                liftedFn =
                    MetallicFunction
                        { mfName = liftedName
                        , mfParams = liftedParams
                        , mfReturnType = retType
                        , mfBody = lambdaBody'
                        , mfMetadata =
                            MetallicFunctionMetadata
                                { mfmOriginalName = []
                                , mfmConstraints = []
                                , mfmInstanceInfo = Nothing
                                , mfmClosureInfo = Just (ClosureFunctionInfo freeVarsList)
                                , mfmIsInline = False
                                }
                        }

            addLiftedFunction liftedFn

            -- Register this closure for later call sites
            modify $ \st -> st{lsClosures = Map.insert name (ClosureInfo liftedName freeVarsList) (lsClosures st)}

            -- Uniform closure calling convention: ALL lambdas become closures
            let closureExpr = MClosure liftedName freeVarsList lambdaTy
            body' <- liftExprLambdas available (Set.insert name bound) body
            pure $ MLet name closureExpr body' ty
        _ -> do
            val' <- liftExprLambdas available bound val
            body' <- liftExprLambdas available (Set.insert name bound) body
            pure $ MLet name val' body' ty
liftExprLambdas available bound (MLambda params body ty) = do
    globals <- gets lsGlobalNames
    let paramSet = Set.fromList params
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

    lambdaId <- freshLambdaId
    let liftedName = "lambda$" ++ show lambdaId

    -- Use splitFunctionType with actual param count, not full uncurrying
    let (paramTypes, retType) = splitFunctionType (length params) ty
        originalParams = zip params paramTypes
        -- Uniform calling convention: closure_self is first param
        liftedParams = ("closure_self", closurePtrType) : originalParams
        liftedFn =
            MetallicFunction
                { mfName = liftedName
                , mfParams = liftedParams
                , mfReturnType = retType
                , mfBody = body'
                , mfMetadata =
                    MetallicFunctionMetadata
                        { mfmOriginalName = []
                        , mfmConstraints = []
                        , mfmInstanceInfo = Nothing
                        , mfmClosureInfo = Just (ClosureFunctionInfo freeVarsList)
                        , mfmIsInline = False
                        }
                }

    addLiftedFunction liftedFn

    -- Uniform closure calling convention: ALL lambdas become closures
    pure (MClosure liftedName freeVarsList ty)
liftExprLambdas available bound (MConstruct name tag args ty) =
    MConstruct name tag <$> mapM (liftExprLambdas available bound) args <*> pure ty
liftExprLambdas available bound (MArrayLit elems ty) =
    MArrayLit <$> mapM (liftExprLambdas available bound) elems <*> pure ty
liftExprLambdas available bound (MTuple elems ty) =
    MTuple <$> mapM (liftExprLambdas available bound) elems <*> pure ty
liftExprLambdas available bound (MCase scrutinees arms mdef ty) =
    MCase
        <$> mapM (liftExprLambdas available bound) scrutinees
        <*> mapM (liftArm available bound) arms
        <*> mapM (liftExprLambdas available bound) mdef
        <*> pure ty
  where
    liftArm :: Set.Set String -> Set.Set String -> MCaseArm -> LiftM MCaseArm
    liftArm avail boundVars MCaseArm{mcaPatterns, mcaBody} =
        let binders = concatMap collectBinders mcaPatterns
            boundInArm = Set.union boundVars (Set.fromList binders)
        in MCaseArm mcaPatterns <$> liftExprLambdas avail boundInArm mcaBody
liftExprLambdas available bound (MIf ifCond ifBlock elseBlock ty) =
    MIf
        <$> liftExprLambdas available bound ifCond
        <*> liftExprLambdas available bound ifBlock
        <*> liftExprLambdas available bound elseBlock
        <*> pure ty
liftExprLambdas available bound (MFieldAccess e idx ty) =
    (\e' -> MFieldAccess e' idx ty) <$> liftExprLambdas available bound e
liftExprLambdas available bound (MCompose stmts ty) =
    (MCompose . fst <$> liftComposeLambdas available bound stmts) <*> pure ty
liftExprLambdas _ _ e@(MPanic _ _) = pure e
-- MClosure is already lifted, just pass through
liftExprLambdas _ _ e@(MClosure{}) = pure e

liftComposeLambdas :: Set.Set String -> Set.Set String -> [MetallicComposeStmt] -> LiftM ([MetallicComposeStmt], Set.Set String)
liftComposeLambdas _ bound [] = pure ([], bound)
liftComposeLambdas available bound (stmt : rest) = case stmt of
    MCBind name e -> do
        e' <- liftExprLambdas available bound e
        (rest', bound'') <- liftComposeLambdas available (Set.insert name bound) rest
        pure (MCBind name e' : rest', bound'')
    MCLet name e -> do
        e' <- liftExprLambdas available bound e
        (rest', bound'') <- liftComposeLambdas available (Set.insert name bound) rest
        pure (MCLet name e' : rest', bound'')
    MCExpr e -> do
        e' <- liftExprLambdas available bound e
        (rest', bound'') <- liftComposeLambdas available bound rest
        pure (MCExpr e' : rest', bound'')

freshLambdaId :: LiftM Int
freshLambdaId = do
    st <- get
    let i = lsNextLambdaId st
    put st{lsNextLambdaId = i + 1}
    pure i

freshTmpName :: LiftM String
freshTmpName = do
    i <- freshLambdaId
    pure $ "closure_tmp$" ++ show i

addLiftedFunction :: MetallicFunction -> LiftM ()
addLiftedFunction fn = modify $ \st ->
    st
        { lsLiftedFunctions = fn : lsLiftedFunctions st
        , lsGlobalNames = Set.insert (mfName fn) (lsGlobalNames st)
        }

computeFreeVarsWithTypes :: MetallicExpr -> Map.Map String Type
computeFreeVarsWithTypes (MVar v t) = Map.singleton v t
computeFreeVarsWithTypes (MLit _) = Map.empty
computeFreeVarsWithTypes (MCall callee args _) =
    Map.unions (computeFreeVarsWithTypes callee : map computeFreeVarsWithTypes args)
computeFreeVarsWithTypes (MTypeApp e _ _) = computeFreeVarsWithTypes e
computeFreeVarsWithTypes (MLet name val body _) =
    Map.union (computeFreeVarsWithTypes val) (Map.delete name (computeFreeVarsWithTypes body))
computeFreeVarsWithTypes (MLambda params body _) =
    foldr Map.delete (computeFreeVarsWithTypes body) params
computeFreeVarsWithTypes (MConstruct _ _ args _) = Map.unions (map computeFreeVarsWithTypes args)
computeFreeVarsWithTypes (MArrayLit elems _) = Map.unions (map computeFreeVarsWithTypes elems)
computeFreeVarsWithTypes (MTuple elems _) = Map.unions (map computeFreeVarsWithTypes elems)
computeFreeVarsWithTypes (MCase scrutinees arms mdef _) =
    let scrFree = Map.unions (map computeFreeVarsWithTypes scrutinees)
        armsFree =
            Map.unions
                [ foldr Map.delete (computeFreeVarsWithTypes (mcaBody arm)) (concatMap collectBinders (mcaPatterns arm))
                | arm <- arms
                ]
        defFree = maybe Map.empty computeFreeVarsWithTypes mdef
    in Map.unions [scrFree, armsFree, defFree]
computeFreeVarsWithTypes (MFieldAccess e _ _) = computeFreeVarsWithTypes e
computeFreeVarsWithTypes (MCompose stmts _) =
    let step (acc, bound) stmt =
            case stmt of
                MCBind name e ->
                    let freeInE = computeFreeVarsWithTypes e
                        filtered = foldr Map.delete freeInE (Set.toList bound)
                    in (Map.union acc filtered, Set.insert name bound)
                MCLet name e ->
                    let freeInE = computeFreeVarsWithTypes e
                        filtered = foldr Map.delete freeInE (Set.toList bound)
                    in (Map.union acc filtered, Set.insert name bound)
                MCExpr e ->
                    let freeInE = computeFreeVarsWithTypes e
                        filtered = foldr Map.delete freeInE (Set.toList bound)
                    in (Map.union acc filtered, bound)
        (fv, _) = foldl step (Map.empty, Set.empty) stmts
    in fv
computeFreeVarsWithTypes (MIf cond ifB elseB _) =
    Map.unions (map computeFreeVarsWithTypes [cond, ifB, elseB])
computeFreeVarsWithTypes (MPanic _ _) = Map.empty
computeFreeVarsWithTypes (MClosure _ capturedVars _) =
    Map.fromList capturedVars

collectBinders :: Pattern -> [String]
collectBinders (PVar v _) = [v]
collectBinders PWildcard{} = []
collectBinders PLit{} = []
collectBinders (PAs v p _) = v : collectBinders p
collectBinders (PConstructor _ ps _) = concatMap collectBinders ps
collectBinders (PTuple ps _) = concatMap collectBinders ps
collectBinders (PArray ps _) = concatMap collectBinders ps

{- | Split a function type based on a specific arity (number of parameters)
Unlike uncurryFunctionType, this stops after taking n parameters
-}
splitFunctionType :: Int -> Type -> ([Type], Type)
splitFunctionType 0 ty = ([], ty)
splitFunctionType n (TArrow argTy restTy) =
    let (args, ret) = splitFunctionType (n - 1) restTy
    in (argTy : args, ret)
splitFunctionType _ ty = ([], ty)
