{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Alloy.Lower (
    lowerAlloyModule,
) where

import Alloy.Build (
    AlloyBuilder,
    beginBlock,
    beginFunctionFull,
    emitEffect,
    emitLetTmp,
    endFunction,
    freshBlockName,
    runAlloyBuilder,
    terminate,
 )
import Alloy.Ir
import Circuit.Decisions (
    Accessor (..),
    Constructor (..),
    DecisionTree (..),
    compile,
    mkPatternMatrix,
 )
import Control.Applicative ((<|>))
import Control.Monad (forM)
import Control.Monad.State.Strict
import qualified Data.Map.Strict as Map
import Metal.Expr (
    MCaseArm (..),
    MetallicExpr (..),
    MetallicLiteral (..),
 )
import Metal.Function (
    MetallicFunction (..),
 )
import Metal.Metadata (
    ClosureFunctionInfo (..),
    MetallicFunctionMetadata (..),
 )
import Metal.Module (
    MetallicConstructor (..),
    MetallicModule (..),
    MetallicTypeDef (..),
 )
import Metal.MonadProfile (
    MonadProfiles,
    buildMonadProfiles,
 )
import Syntax.Patterns (
    Literal (..),
    Pattern (..),
 )
import Typing.Types (
    Type (..),
    boolType,
    byteType,
    intType,
    strType,
 )

-- | Info about a closure binding
data ClosureInfo = ClosureInfo
    { ciEnvSize :: !Int -- number of captured env values
    , ciFuncName :: !String -- underlying lifted function name
    }
    deriving (Show, Eq)

data LEnv = LEnv
    { leVars :: Map.Map String AOperand
    , leClosures :: Map.Map String ClosureInfo -- variable name -> closure info
    , leClosureReturningFns :: Map.Map String ClosureReturnInfo -- function name -> closure return info
    , leCtorTags :: Map.Map String Int
    , leCtorFields :: Map.Map String [Type]
    , leProfiles :: MonadProfiles
    }

type Lower a = StateT LEnv AlloyBuilder a

lowerAlloyModule :: String -> MetallicModule -> AlloyModule
lowerAlloyModule modName mm =
    let ctorTags = buildCtorTagMap mm
        ctorFields = buildCtorFieldMap mm
        profiles = buildMonadProfiles mm
        closureRetFns = buildClosureReturningFnsMap (mmFunctions mm)
        action = mapM_ (lowerFunction ctorTags ctorFields profiles closureRetFns) (mmFunctions mm)
        (_unit, mdl) = runAlloyBuilder modName (mmTypeClasses mm) action
    in mdl

-- | Info about what a function returns if it returns a closure
data ClosureReturnInfo = ClosureReturnInfo
    { criEnvSize :: !Int -- env size of the returned closure
    , criLiftedFn :: !String -- the lifted function the closure points to
    }
    deriving (Show, Eq)

-- | Build a map of function names to info about closures they return
buildClosureReturningFnsMap :: [MetallicFunction] -> Map.Map String ClosureReturnInfo
buildClosureReturningFnsMap fns =
    Map.fromList
        [ (mfName fn, info)
        | fn <- fns
        , Just info <- [getClosureReturnInfo (mfBody fn)]
        ]
  where
    getClosureReturnInfo :: MetallicExpr -> Maybe ClosureReturnInfo
    getClosureReturnInfo (MClosure liftedName capturedVars _) =
        Just $ ClosureReturnInfo (length capturedVars) liftedName
    getClosureReturnInfo _ = Nothing

lowerFunction :: Map.Map String Int -> Map.Map String [Type] -> MonadProfiles -> Map.Map String ClosureReturnInfo -> MetallicFunction -> AlloyBuilder ()
lowerFunction ctorTags ctorFields profiles closureRetFns MetallicFunction{mfName, mfParams, mfReturnType, mfBody, mfMetadata} = do
    let constraints = mfmConstraints mfMetadata
    let isInline = mfmIsInline mfMetadata
    beginFunctionFull mfName mfParams mfReturnType constraints isInline
    let entryName = "entry"
    beginBlock entryName []

    -- For lifted lambdas with closure_self parameter, extract captured env vars
    envBindings <- case mfmClosureInfo mfMetadata of
        Just (ClosureFunctionInfo capturedVars) -> do
            -- closure_self is the first parameter
            let closureSelfOp = OpVar "closure_self"
            -- Extract each captured variable from the closure environment
            forM (zip [0 ..] capturedVars) $ \(idx, (varName, varTy)) -> do
                extractedName <- emitLetTmp varTy (OpClosureGetEnv closureSelfOp idx)
                pure (varName, OpVar extractedName)
        Nothing -> pure []

    let initialEnv =
            LEnv
                { leVars = Map.fromList ([(pname, OpVar pname) | (pname, _pty) <- mfParams] ++ envBindings)
                , leClosures = Map.empty
                , leClosureReturningFns = closureRetFns
                , leCtorTags = ctorTags
                , leCtorFields = ctorFields
                , leProfiles = profiles
                }

    retval <- evalStateT (lowerExpr mfBody) initialEnv
    terminate (ARet (Just retval))
    endFunction

lowerExpr :: MetallicExpr -> Lower AOperand
lowerExpr (MVar name _ty) = do
    env <- gets leVars
    pure $ Map.findWithDefault (OpVar name) name env
lowerExpr (MLit lit) =
    pure $ OpConst (lowerLiteral lit)
lowerExpr (MLet name valExpr bodyExpr _ty) = do
    v <- lowerExpr valExpr
    -- Track closures for proper call handling
    case valExpr of
        MClosure liftedName capturedVars _ ->
            withClosureBinding name liftedName (length capturedVars) v (lowerExpr bodyExpr)
        MCall callee _ _ -> do
            closureRetFns <- gets leClosureReturningFns
            closureEnv <- gets leClosures
            case stripTypeApps callee of
                MVar fnName _ | Map.notMember fnName closureEnv -> do
                    -- Direct call to a known function - check if it returns a closure
                    case Map.lookup fnName closureRetFns of
                        Just (ClosureReturnInfo envSize liftedFn) ->
                            withClosureBinding name liftedFn envSize v (lowerExpr bodyExpr)
                        Nothing -> withBinding name v (lowerExpr bodyExpr)
                MVar fnName _ | Just (ClosureInfo _ funcName) <- Map.lookup fnName closureEnv -> do
                    -- Call to a closure - check if the underlying func returns a closure
                    case Map.lookup funcName closureRetFns of
                        Just (ClosureReturnInfo envSize liftedFn) ->
                            withClosureBinding name liftedFn envSize v (lowerExpr bodyExpr)
                        Nothing -> withBinding name v (lowerExpr bodyExpr)
                _ -> withBinding name v (lowerExpr bodyExpr)
        _ -> withBinding name v (lowerExpr bodyExpr)
  where
    stripTypeApps (MTypeApp e _ _) = stripTypeApps e
    stripTypeApps e = e
lowerExpr (MLambda _paramNames _body ty) = do
    -- todo: create a closure value, allocate env, etc etc
    failLower ("Lambda lowering requires closure conversion; lambdas should be lifted to top-level before Alloy lowering. Lambda type: " ++ show ty)
lowerExpr (MClosure liftedName capturedVars ty) = do
    -- Allocate closure with the lifted function and captured environment
    capturedOps <- mapM (\(n, _t) -> lowerExpr (MVar n _t)) capturedVars
    let arity = countArityFromType ty
        envSize = length capturedVars
    closureName <- lift $ emitLetTmp ty (OpAllocClosure (OpVar liftedName) arity envSize)
    -- Set each captured variable in the closure's environment
    mapM_
        ( \(idx, capturedOp) ->
            lift $ emitEffect (EffClosureSetEnv (OpVar closureName) idx capturedOp)
        )
        (zip [0 ..] capturedOps)
    pure (OpVar closureName)
  where
    countArityFromType :: Type -> Int
    countArityFromType (TArrow _ rest) = 1 + countArityFromType rest
    countArityFromType _ = 0
lowerExpr (MConstruct typeName tag fields ty) = do
    ops <- mapM lowerExpr fields
    tmp <- lift $ emitLetTmp ty (OpConstruct typeName tag ops)
    pure (OpVar tmp)
lowerExpr (MCall callee args ty) = do
    argOps <- mapM lowerExpr args
    env <- gets leVars
    closureEnv <- gets leClosures
    case stripTypeApps callee of
        MVar fname _ | Map.notMember fname env -> do
            -- Direct call to a known function (not a local variable)
            tmp <- lift $ emitLetTmp ty (OpCall (Direct fname) argOps)
            pure (OpVar tmp)
        MVar fname _ | Just (ClosureInfo _envSize funcName) <- Map.lookup fname closureEnv -> do
            -- Uniform calling convention: pass closure as first arg
            -- The lifted function extracts its own env from closure_self
            closureOp <- lowerExpr callee
            -- Get function pointer from closure
            funcPtrName <- lift $ emitLetTmp (TArrow intType intType) (OpClosureGetFunc closureOp)
            -- Call with closure as first arg (uniform convention)
            tmp <- lift $ emitLetTmp ty (OpCall (Indirect (OpVar funcPtrName)) (closureOp : argOps))
            -- Check if the underlying function returns a closure - if so, track it
            closureRetFns <- gets leClosureReturningFns
            case Map.lookup funcName closureRetFns of
                Just (ClosureReturnInfo retEnvSize retLiftedFn) -> do
                    -- The result is a closure - add to tracking
                    let info = ClosureInfo retEnvSize retLiftedFn
                    modify (\st -> st{leClosures = Map.insert tmp info (leClosures st)})
                Nothing -> pure ()
            pure (OpVar tmp)
        MVar fname calleeTy
            | Map.member fname env
            , isFunctionType calleeTy -> do
                -- Indirect call through function-typed variable (e.g., higher-order function parameter)
                -- Uniform calling convention: treat as closure, pass as first arg
                closureOp <- lowerExpr callee
                -- Get function pointer from closure
                funcPtrName <- lift $ emitLetTmp (TArrow intType intType) (OpClosureGetFunc closureOp)
                -- Call with closure as first arg
                tmp <- lift $ emitLetTmp ty (OpCall (Indirect (OpVar funcPtrName)) (closureOp : argOps))
                pure (OpVar tmp)
        _ -> do
            -- Other indirect calls (shouldn't happen in well-formed code)
            calOp <- lowerExpr callee
            tmp <- lift $ emitLetTmp ty (OpCall (Indirect calOp) argOps)
            pure (OpVar tmp)
  where
    stripTypeApps (MTypeApp e _ _) = stripTypeApps e
    stripTypeApps e = e
    isFunctionType (TArrow _ _) = True
    isFunctionType _ = False
lowerExpr (MTypeApp e _tys _ty) =
    lowerExpr e
lowerExpr (MArrayLit elems ty) = do
    ops <- mapM lowerExpr elems
    tmp <- lift $ emitLetTmp ty (OpMakeArray ops)
    pure (OpVar tmp)
lowerExpr (MTuple elems ty) = do
    ops <- mapM lowerExpr elems

    tmp <- lift $ emitLetTmp ty (OpMakeTuple ops)

    pure (OpVar tmp)
-- Full pattern match lowering using decision trees and CFG.

lowerExpr (MCase scrutinees arms _defaultExpr resultTy) = do
    scrOps <- mapM lowerExpr scrutinees
    lowerCase scrOps arms resultTy
lowerExpr (MFieldAccess base idx ty) = do
    baseOp <- lowerExpr base
    tmp <- lift $ emitLetTmp ty (OpProject baseOp idx)
    pure (OpVar tmp)
lowerExpr (MIf ifCond ifBlock elseBlock ty) = do
    condOp <- lowerExpr ifCond

    thenName <- lift freshBlockName
    elseName <- lift freshBlockName
    joinName <- lift freshBlockName

    lift $ terminate (ACondBr condOp thenName [] elseName [])

    lift $ beginBlock thenName []
    thenVal <- lowerExpr ifBlock
    lift $ terminate (ABr joinName [thenVal])

    lift $ beginBlock elseName []
    elseVal <- lowerExpr elseBlock
    lift $ terminate (ABr joinName [elseVal])

    let resParam = "res"
    lift $ beginBlock joinName [(resParam, ty)]
    pure (OpVar resParam)
lowerExpr (MPanic msg _ty) =
    failLower ("Lowering of panic in expression position is not implemented: " ++ msg)

lowerLiteral :: MetallicLiteral -> AConst
lowerLiteral (MInt i) = CInt i
lowerLiteral (MBool b) = CBool b
lowerLiteral (MString s) = CString s

buildCtorFieldMap :: MetallicModule -> Map.Map String [Type]
buildCtorFieldMap mm =
    Map.fromList
        [ (mcName c, mcFields c)
        | MAlgebraicType{mtConstructors = ctors} <- mmTypes mm
        , c <- ctors
        ]

buildCtorTagMap :: MetallicModule -> Map.Map String Int
buildCtorTagMap mm =
    Map.fromList
        [ (mcName c, fromIntegral (mcTag c))
        | MAlgebraicType{mtConstructors = ctors} <- mmTypes mm
        , c <- ctors
        ]

getCtorTag :: String -> Lower Int
getCtorTag ctor = do
    env <- get
    case Map.lookup ctor (leCtorTags env) of
        Just n -> pure n
        Nothing -> failLower ("Unknown constructor tag for: " ++ ctor)

lowerCase :: [AOperand] -> [MCaseArm] -> Type -> Lower AOperand
lowerCase scrOps arms resultTy = do
    let patterns = map mcaPatterns arms
        matrix = mkPatternMatrix (zip patterns [0 .. length patterns - 1])
        tree = compile matrix
    rootName <- lift freshBlockName
    joinName <- lift freshBlockName
    lift $ terminate (ABr rootName [])
    lift $ beginBlock rootName []
    codegenDecisionTree scrOps arms tree joinName resultTy
    let resParam = "res"
    lift $ beginBlock joinName [(resParam, resultTy)]
    pure (OpVar resParam)

codegenDecisionTree :: [AOperand] -> [MCaseArm] -> DecisionTree -> BlockName -> Type -> Lower ()
codegenDecisionTree scrOps arms node joinName resultTy =
    case node of
        Fail -> lift $ terminate AUnreachable
        Leaf i -> do
            let MCaseArm{mcaPatterns = pats, mcaBody = body} = arms !! i
                varTypes = collectVarTypesFromBody body
            binds <- bindPatterns pats scrOps varTypes
            val <- withBindings binds (lowerExpr body)
            lift $ terminate (ABr joinName [val])
        Switch accessor branches defCase ->
            lowerSwitch scrOps arms accessor branches defCase joinName resultTy
        Guard{} -> error "todo: support guards"

lowerSwitch ::
    [AOperand] ->
    [MCaseArm] ->
    Accessor ->
    [(Constructor, DecisionTree)] ->
    Maybe DecisionTree ->
    BlockName ->
    Type ->
    Lower ()
lowerSwitch scrOps arms accessor branches defCase joinName resultTy = do
    case branches of
        ((LitCtor lit, _) : _) -> do
            let litTy = case lit of
                    LitInt _ -> intType
                    LitBool _ -> boolType
                    LitString _ -> strType
                accTy = Just litTy
            accOp <- evalAccessorWithType scrOps accessor accTy
            caseBlocks <- mapM (\(LitCtor l, t) -> lift freshBlockName >>= (\(l', b) -> pure (l', b, t)) . (l,)) branches
            defName <- maybe (pure Nothing) (\_ -> Just <$> lift freshBlockName) defCase
            case lit of
                LitInt _ -> do
                    let cases = [(v, bn) | (LitInt v, bn, _) <- caseBlocks]
                    lift $ terminate (ASwitch accOp [(v, bn) | (v, bn) <- cases] defName)
                    mapM_ (\(_v, bn, t) -> lift (beginBlock bn []) >> codegenDecisionTree scrOps arms t joinName resultTy) caseBlocks
                    maybe
                        (pure ())
                        ( \t -> do
                            let Just dn = defName
                            lift (beginBlock dn [])
                            codegenDecisionTree scrOps arms t joinName resultTy
                        )
                        defCase
                LitBool _ -> do
                    let findBool b = [(bn, t) | (LitBool b', bn, t) <- caseBlocks, b' == b]
                        trueBranch = findBool True
                        falseBranch = findBool False
                    (tLbl, tTree) <- case trueBranch of
                        (bn, t) : _ -> pure (bn, t)
                        [] -> case defCase of
                            Just t -> do bn <- lift freshBlockName; pure (bn, t)
                            Nothing -> do bn <- lift freshBlockName; pure (bn, Fail)
                    (fLbl, fTree) <- case falseBranch of
                        (bn, t) : _ -> pure (bn, t)
                        [] -> case defCase of
                            Just t -> do bn <- lift freshBlockName; pure (bn, t)
                            Nothing -> do bn <- lift freshBlockName; pure (bn, Fail)
                    lift $ terminate (ACondBr accOp tLbl [] fLbl [])
                    lift $ beginBlock tLbl []
                    codegenDecisionTree scrOps arms tTree joinName resultTy
                    lift $ beginBlock fLbl []
                    codegenDecisionTree scrOps arms fTree joinName resultTy
                LitString _ -> do
                    let go [] =
                            case defCase of
                                Nothing -> lift $ terminate AUnreachable
                                Just t -> do
                                    dn <- lift freshBlockName
                                    lift $ terminate (ABr dn [])
                                    lift $ beginBlock dn []
                                    codegenDecisionTree scrOps arms t joinName resultTy
                        go ((LitString s, bn, t) : rest) = do
                            name <- lift $ emitLetTmp boolType (OpCmp CEq accOp (OpConst (CString s)))
                            case rest of
                                [] ->
                                    case defCase of
                                        Nothing -> do
                                            lift $ terminate (ACondBr (OpVar name) bn [] bn [])
                                            lift $ beginBlock bn []
                                            codegenDecisionTree scrOps arms t joinName resultTy
                                        Just tDef -> do
                                            dn <- lift freshBlockName
                                            lift $ terminate (ACondBr (OpVar name) bn [] dn [])
                                            lift $ beginBlock bn []
                                            codegenDecisionTree scrOps arms t joinName resultTy
                                            lift $ beginBlock dn []
                                            codegenDecisionTree scrOps arms tDef joinName resultTy
                                _ -> do
                                    nextT <- lift freshBlockName
                                    lift $ terminate (ACondBr (OpVar name) bn [] nextT [])
                                    lift $ beginBlock bn []
                                    codegenDecisionTree scrOps arms t joinName resultTy
                                    lift $ beginBlock nextT []
                                    go rest
                        go ((LitInt _, _, _) : rest) = go rest
                        go ((LitBool _, _, _) : rest) = go rest
                    go caseBlocks
        ((DataCtor _ _, _) : _) -> do
            case accessor of
                Root i -> do
                    let rootOp = scrOps !! i
                    tagOpName <- lift $ emitLetTmp byteType (OpTagOf rootOp)
                    let tagOp = OpVar tagOpName
                    cases <-
                        mapM
                            (\(DataCtor nm _, t) -> do tg <- getCtorTag nm; bn <- lift freshBlockName; pure (tg, bn, t))
                            branches
                    defName <- maybe (pure Nothing) (\_ -> Just <$> lift freshBlockName) defCase
                    lift $ terminate (ASwitch tagOp [(tg, bn) | (tg, bn, _) <- cases] defName)
                    mapM_ (\(_tg, bn, t) -> lift (beginBlock bn []) >> codegenDecisionTree scrOps arms t joinName resultTy) cases
                    maybe
                        (pure ())
                        ( \t -> do
                            let Just dn = defName
                            lift (beginBlock dn [])
                            codegenDecisionTree scrOps arms t joinName resultTy
                        )
                        defCase
                _ -> failLower "Nested constructor switching on field accessors is not supported without field types"
        ((TupleCtor _, t) : _) | length branches == 1 -> codegenDecisionTree scrOps arms t joinName resultTy
        _ -> failLower "Unsupported switch pattern in decision tree"

evalAccessorWithType :: [AOperand] -> Accessor -> Maybe Type -> Lower AOperand
evalAccessorWithType scrOps (Root i) _ = pure (scrOps !! i)
evalAccessorWithType scrOps (Field acc idx) (Just ty) = do
    base <- evalAccessorWithType scrOps acc Nothing
    tmp <- lift $ emitLetTmp ty (OpProject base idx)
    pure (OpVar tmp)
evalAccessorWithType scrOps (TupleElem acc i) (Just ty) = do
    base <- evalAccessorWithType scrOps acc Nothing
    tmp <- lift $ emitLetTmp ty (OpProject base i)
    pure (OpVar tmp)
evalAccessorWithType scrOps (ArrayElem acc i) (Just ty) = do
    base <- evalAccessorWithType scrOps acc Nothing
    let idx = OpConst (CInt (fromIntegral i))
    tmp <- lift $ emitLetTmp ty (OpIndex base idx)
    pure (OpVar tmp)
evalAccessorWithType _ _ Nothing =
    failLower "Cannot project field without knowing its type"

collectVarTypesFromBody :: MetallicExpr -> Map.Map String Type
collectVarTypesFromBody = go Map.empty
  where
    go acc (MVar v ty) = Map.insertWith (\_ old -> old) v ty acc
    go acc (MLit _) = acc
    go acc (MCall f args _ty) = foldl go (go acc f) args
    go acc (MTypeApp e _ _) = go acc e
    go acc (MLet _ v b _) = go (go acc v) b
    go acc (MLambda _ body _) = go acc body
    go acc (MConstruct _ _ fields _) = foldl go acc fields
    go acc (MArrayLit elems _) = foldl go acc elems
    go acc (MTuple elems _) = foldl go acc elems
    go acc (MCase scr arms mdef _) =
        let acc' = foldl go acc scr
            accArms = foldl (\a (MCaseArm{mcaBody = body}) -> go a body) acc' arms
        in maybe accArms (go accArms) mdef
    go acc (MFieldAccess e _ _) = go acc e
    go acc (MIf c t f _) = go (go (go acc c) t) f
    go acc (MPanic _ _) = acc
    go acc (MClosure _ capturedVars _) =
        foldl (\a (n, ty) -> Map.insertWith (\_ old -> old) n ty a) acc capturedVars

patternHasBinder :: Pattern -> Bool
patternHasBinder (PVar{}) = True
patternHasBinder (PAs _ p _) = patternHasBinder p
patternHasBinder (PConstructor _ ps _) = any patternHasBinder ps
patternHasBinder (PTuple ps _) = any patternHasBinder ps
patternHasBinder (PArray ps _) = any patternHasBinder ps
patternHasBinder _ = False

bindPatterns ::
    [Pattern] ->
    [AOperand] ->
    Map.Map String Type ->
    Lower [(String, AOperand)]
bindPatterns [] [] _ = pure []
bindPatterns (p : ps) (o : os) varTypes = do
    here <- bindOne p o varTypes
    rest <- bindPatterns ps os varTypes
    pure (here ++ rest)
bindPatterns _ _ _ = failLower "Arity mismatch in pattern binding"

bindOne :: Pattern -> AOperand -> Map.Map String Type -> Lower [(String, AOperand)]
bindOne (PVar v _) op _ = pure [(v, op)]
bindOne PWildcard{} _ _ = pure []
bindOne (PLit{}) _ _ = pure []
bindOne (PAs v p _) op vt = do
    more <- bindOne p op vt
    pure ((v, op) : more)
bindOne (PConstructor ctorName sub _) op vt = bindPositional sub
  where
    bindPositional [] = pure []
    bindPositional ps = do
        fieldBinds <- mapM bindField (zip [0 ..] ps)
        pure (concat fieldBinds)
    bindField (idx, sp) =
        if patternHasBinder sp
            then do
                let vars = collectVars sp
                    mty = foldl (\acc v -> acc <|> Map.lookup v vt) Nothing vars
                ty <- case mty of
                    Just t -> pure t
                    Nothing -> do
                        env <- get
                        case Map.lookup ctorName (leCtorFields env) of
                            Just fields ->
                                case drop idx fields of
                                    (t : _) -> pure t
                                    [] -> failLower ("Alloy.Lower: constructor " ++ ctorName ++ " has no field at index " ++ show idx)
                            Nothing -> failLower ("Unable to infer field type for pattern binder for constructor " ++ ctorName)
                tmp <- lift $ emitLetTmp ty (OpProject op idx)
                bindOne sp (OpVar tmp) vt
            else pure []
    collectVars (PVar v _) = [v]
    collectVars (PAs v p _) = v : collectVars p
    collectVars (PConstructor _ ps _) = concatMap collectVars ps
    collectVars (PTuple ps _) = concatMap collectVars ps
    collectVars (PArray ps _) = concatMap collectVars ps
    collectVars _ = []
bindOne (PTuple sub s) op vt = bindOne (PConstructor "" sub s) op vt
bindOne (PArray{}) _ _ = pure []

withBinding :: String -> AOperand -> Lower a -> Lower a
withBinding name op action = do
    old <- get
    let newEnv = Map.insert name op (leVars old)
    put old{leVars = newEnv}
    res <- action
    modify (const old)
    pure res

withClosureBinding :: String -> String -> Int -> AOperand -> Lower a -> Lower a
withClosureBinding name funcName envSize op action = do
    old <- get
    let newVars = Map.insert name op (leVars old)
        newClosures = Map.insert name (ClosureInfo envSize funcName) (leClosures old)
    put old{leVars = newVars, leClosures = newClosures}
    res <- action
    modify (const old)
    pure res

withBindings :: [(String, AOperand)] -> Lower a -> Lower a
withBindings kvs action = do
    old <- get
    let newEnv = foldr (uncurry Map.insert) (leVars old) kvs
    put old{leVars = newEnv}
    res <- action
    modify (const old)
    pure res

failLower :: String -> Lower a
failLower msg = lift $ error ("Alloy.Lower: " ++ msg)
