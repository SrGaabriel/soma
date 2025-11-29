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
                Just (ClosureInfo liftedName capturedVars) -> do
                    let capturedArgs = [MVar n t | (n, t) <- capturedVars]
                        allArgs = capturedArgs ++ args'
                        liftedFnType = foldr TArrow ty (map snd capturedVars ++ map getType args')
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

            let (paramTypes, retType) = uncurryFunctionType lambdaTy
                freeVarParams = freeVarsList
                originalParams = zip params paramTypes
                liftedParams = freeVarParams ++ originalParams
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
                                }
                        }

            addLiftedFunction liftedFn

            let capturedArgs = [MVar n t | (n, t) <- freeVarsList]
                allArgs = capturedArgs ++ args'
                fullType = foldr TArrow retType (map snd liftedParams)
            pure $ MCall (MVar liftedName fullType) allArgs ty
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
                freeVarsList =
                    [ (n, varTy)
                    | (n, varTy) <- Map.toList freeVarsWithTypes
                    , not (Set.member n paramSet)
                    , not (Set.member n bound)
                    , not (Set.member n globals)
                    ]

            let newAvailable = Set.union paramSet (Set.union available bound)
            lambdaBody' <- liftExprLambdas newAvailable Set.empty lambdaBody

            lambdaId <- freshLambdaId
            let liftedName = "lambda$" ++ show lambdaId

            let (paramTypes, retType) = uncurryFunctionType lambdaTy
                freeVarParams = freeVarsList
                originalParams = zip params paramTypes
                liftedParams = freeVarParams ++ originalParams
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
                                }
                        }

            addLiftedFunction liftedFn

            if null freeVarsList
                then do
                    body' <- liftExprLambdas available (Set.insert name bound) body
                    pure $ MLet name (MVar liftedName lambdaTy) body' ty
                else do
                    let closureInfo = ClosureInfo liftedName freeVarsList
                    modify $ \st -> st{lsClosures = Map.insert name closureInfo (lsClosures st)}
                    body' <- liftExprLambdas available (Set.insert name bound) body
                    modify $ \st -> st{lsClosures = Map.delete name (lsClosures st)}
                    pure body'
        _ -> do
            val' <- liftExprLambdas available bound val
            body' <- liftExprLambdas available (Set.insert name bound) body
            pure $ MLet name val' body' ty
liftExprLambdas available bound (MLambda params body ty) = do
    globals <- gets lsGlobalNames
    let paramSet = Set.fromList params
        freeVarsWithTypes = computeFreeVarsWithTypes body
        freeVarsList =
            [ (name, varTy)
            | (name, varTy) <- Map.toList freeVarsWithTypes
            , not (Set.member name paramSet)
            , not (Set.member name available)
            , not (Set.member name bound)
            , not (Set.member name globals)
            ]

    let newAvailable = Set.union paramSet (Set.union available bound)
    body' <- liftExprLambdas newAvailable Set.empty body

    lambdaId <- freshLambdaId
    let liftedName = "lambda$" ++ show lambdaId

    let (paramTypes, retType) = uncurryFunctionType ty
        freeVarParams = freeVarsList
        originalParams = zip params paramTypes
        liftedParams = freeVarParams ++ originalParams
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
                        }
                }

    addLiftedFunction liftedFn

    if null freeVarsList
        then pure (MVar liftedName ty)
        else
            error
                $ "Standalone lambda with free variables passed as value is not supported. "
                    ++ "Lambda captures: "
                    ++ show (map fst freeVarsList)
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

addLiftedFunction :: MetallicFunction -> LiftM ()
addLiftedFunction fn = modify $ \st ->
    st
        { lsLiftedFunctions = fn : lsLiftedFunctions st
        , lsGlobalNames = Set.insert (mfName fn) (lsGlobalNames st)
        }

computeFreeVars :: MetallicExpr -> Set.Set String
computeFreeVars = Map.keysSet . computeFreeVarsWithTypes

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

collectBinders :: Pattern -> [String]
collectBinders (PVar v _) = [v]
collectBinders PWildcard{} = []
collectBinders PLit{} = []
collectBinders (PAs v p _) = v : collectBinders p
collectBinders (PConstructor _ ps _) = concatMap collectBinders ps
collectBinders (PTuple ps _) = concatMap collectBinders ps
collectBinders (PArray ps _) = concatMap collectBinders ps

uncurryFunctionType :: Type -> ([Type], Type)
uncurryFunctionType ty = go ty []
  where
    go (TArrow t1 t2) acc = go t2 (acc ++ [t1])
    go t acc = (acc, t)
