{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Alloy.Lower (
    lowerAlloyModule,
) where

import Control.Applicative ((<|>))
import Control.Monad.State.Strict
import qualified Data.Map.Strict as Map

import Alloy.Decisions (
    Accessor (..),
    Constructor (..),
    DecisionTree (..),
    compile,
    mkPatternMatrix,
 )

import Alloy.Build (
    AlloyBuilder,
    beginBlock,
    beginFunction,
    emitLetTmp,
    endFunction,
    freshBlockName,
    runAlloyBuilder,
    terminate,
 )
import Alloy.Ir

import Metal.Expr (
    MCaseArm (..),
    MetallicComposeStmt (..),
    MetallicExpr (..),
    MetallicLiteral (..),
    getMetallicExprType,
 )

import Metal.Function (
    MetallicFunction (..),
 )
import Metal.MonadProfile (
    MonadProfile (..),
    MonadProfiles,
    buildMonadProfiles,
    lookupProfile,
 )

import Metal.Module (
    MetallicConstructor (..),
    MetallicModule (..),
    MetallicTypeDef (..),
 )
import Syntax.Patterns (
    Literal (..),
    Pattern (..),
 )

import Typing.Types (
    TyConstructor (..),
    Type (..),
    boolType,
    intType,
    strType,
 )

data LEnv = LEnv
    { leVars :: Map.Map String AOperand
    , leCtorTags :: Map.Map String Integer
    , leCtorFields :: Map.Map String [Type]
    , leProfiles :: MonadProfiles
    }

type Lower a = StateT LEnv AlloyBuilder a

lowerAlloyModule :: String -> MetallicModule -> AlloyModule
lowerAlloyModule modName mm =
    let ctorTags = buildCtorTagMap mm

        ctorFields = buildCtorFieldMap mm
        profiles = buildMonadProfiles mm
        action = mapM_ (lowerFunction ctorTags ctorFields profiles) (mmFunctions mm)

        (_unit, mdl) = runAlloyBuilder modName action
    in mdl

lowerFunction :: Map.Map String Integer -> Map.Map String [Type] -> MonadProfiles -> MetallicFunction -> AlloyBuilder ()
lowerFunction ctorTags ctorFields profiles MetallicFunction{mfName, mfParams, mfReturnType, mfBody} = do
    beginFunction mfName mfParams mfReturnType
    let entryName = "entry"
    beginBlock entryName []

    let initialEnv =
            LEnv
                { leVars = Map.fromList [(pname, OpVar pname) | (pname, _pty) <- mfParams]
                , leCtorTags = ctorTags
                , leCtorFields = ctorFields
                , leProfiles = profiles
                }

    retval <- evalStateT (lowerExpr mfBody) initialEnv
    terminate (ARet (Just retval))
    endFunction

-- Lower a HIR expression to an Alloy operand, emitting instructions as needed
lowerExpr :: MetallicExpr -> Lower AOperand
lowerExpr (MVar name _ty) = do
    env <- gets leVars
    pure $ Map.findWithDefault (OpVar name) name env
lowerExpr (MLit lit) =
    pure $ OpConst (lowerLiteral lit)
lowerExpr (MLet name valExpr bodyExpr _ty) = do
    v <- lowerExpr valExpr
    withBinding name v (lowerExpr bodyExpr)
lowerExpr (MLambda _paramNames _body ty) = do
    -- todo: create a closure value, allocate env, etc etc
    failLower ("Lambda lowering requires closure conversion; lambdas should be lifted to top-level before Alloy lowering. Lambda type: " ++ show ty)
lowerExpr (MConstruct typeName tag fields ty) = do
    ops <- mapM lowerExpr fields
    tmp <- lift $ emitLetTmp ty (OpConstruct typeName tag ops)
    pure (OpVar tmp)
lowerExpr (MCall callee args ty) = do
    calOp <- lowerExpr callee
    argOps <- mapM lowerExpr args
    let callable = case callee of
            MVar fname _ -> Direct fname
            _ -> Indirect calOp
    tmp <- lift $ emitLetTmp ty (OpCall callable argOps)
    pure (OpVar tmp)
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
lowerExpr (MCompose stmts ty) =
    lowerCompose stmts ty
-- Full pattern match lowering using decision trees and CFG.

lowerExpr (MCase scrutinees arms _defaultExpr resultTy) = do
    scrOps <- mapM lowerExpr scrutinees
    lowerCase scrOps arms resultTy
lowerExpr (MFieldAccess base idx ty) = do
    baseOp <- lowerExpr base
    tmp <- lift $ emitLetTmp ty (OpProject baseOp idx)
    pure (OpVar tmp)
lowerExpr (MPanic msg _ty) =
    failLower ("Lowering of panic in expression position is not implemented: " ++ msg)

lowerLiteral :: MetallicLiteral -> AConst
lowerLiteral (MInt i) = CInt i
lowerLiteral (MBool b) = CBool b
lowerLiteral (MString s) = CString s

-- Lower a composition block to CFG with short-circuiting for Option/Either.

-- - MCBind x e:

--     * If e has type Option a:
--         - switch on tag(e): None -> short-circuit to join with e

--                             Some v -> bind x = v and continue

--     * If e has type Either l r:

--         - switch on tag(e): Left l  -> short-circuit to join with e

--                             Right v -> bind x = v and continue

--     * Otherwise: strict let-binding x = e and continue

-- - MCLet x e: strict let-binding x = e and continue
-- - MCExpr e: evaluate strictly, discard (unless last), continue
-- Final statement:
--   * If the result type is Optional t: wrap final value as Some (or pass through Optional on short-circuit)
--   * If the result type is Either l r: wrap final value as Right (or pass through Either on short-circuit)
--   * Otherwise: return the plain final value
lowerCompose :: [MetallicComposeStmt] -> Type -> Lower AOperand
lowerCompose [] _ =
    failLower "Alloy.Lower: compose block must contain at least one statement"
lowerCompose stmts resultTy = do
    rootName <- lift freshBlockName
    joinName <- lift freshBlockName
    lift $ terminate (ABr rootName [])
    lift $ beginBlock rootName []
    seqBuild stmts joinName resultTy
    let resParam = "res"
    lift $ beginBlock joinName [(resParam, resultTy)]
    pure (OpVar resParam)
  where
    seqBuild :: [MetallicComposeStmt] -> BlockName -> Type -> Lower ()

    seqBuild [] _ _ = failLower "Alloy.Lower: empty compose sequence after normalization"
    seqBuild [MCExpr e] joinNm resTy = do
        v <- lowerExpr e
        let eTy = getMetallicExprType e
        mProf <- resultProfile resTy

        case mProf of
            Just (ProfileShortCircuit{mpSuccessCtor}) -> do
                -- If the final expression already yields the monadic result type,
                -- do not wrap again. Only wrap when the expression is the payload.
                let eCtor = getTypeCtorName eTy
                let rCtor = getTypeCtorName resTy
                case (eCtor, rCtor) of
                    (Just ec, Just rc)
                        | ec == rc ->
                            lift $ terminate (ABr joinNm [v])
                    _ -> do
                        sTag <- mustTag mpSuccessCtor
                        let ctorName = mpSuccessCtor
                        tmp <- lift $ emitLetTmp resTy (OpConstruct ctorName (fromIntegral sTag) [v])
                        lift $ terminate (ABr joinNm [OpVar tmp])
            _ -> lift $ terminate (ABr joinNm [v])
    seqBuild (MCBind n e : rest) joinNm resTy = do
        v <- lowerExpr e

        let eTy = getMetallicExprType e

        mEProf <- resultProfile eTy
        case mEProf of
            Just (ProfileShortCircuit{mpSuccessCtor = succCtor, mpFailCtor = failCtor}) -> do
                sTag <- mustTag succCtor
                fTag <- mustTag failCtor
                tagNm <- lift $ emitLetTmp intType (OpTagOf v)

                onFail <- lift freshBlockName

                onOk <- lift freshBlockName

                lift $ terminate (ASwitch (OpVar tagNm) [(fTag, onFail), (sTag, onOk)] Nothing)
                lift $ beginBlock onFail []
                mRProf <- resultProfile resTy
                case mRProf of
                    Just (ProfileShortCircuit{}) -> lift $ terminate (ABr joinNm [v])
                    _ -> failLower "Alloy.Lower: bind short-circuit but compose result is not short-circuiting"

                lift $ beginBlock onOk []
                aTy <- payloadType succCtor
                payNm <- lift $ emitLetTmp aTy (OpProject v 0)
                modify (\st -> st{leVars = Map.insert n (OpVar payNm) (leVars st)})

                seqBuild rest joinNm resTy
            _ -> do
                modify (\st -> st{leVars = Map.insert n v (leVars st)})
                seqBuild rest joinNm resTy
    seqBuild (MCLet n e : rest) joinNm resTy = do
        v <- lowerExpr e

        modify (\st -> st{leVars = Map.insert n v (leVars st)})
        seqBuild rest joinNm resTy

    -- MCExpr (non-final): evaluate strictly, discard result
    seqBuild (MCExpr e : rest) joinNm resTy = do
        _ <- lowerExpr e

        seqBuild rest joinNm resTy

    mustTag :: String -> Lower Integer
    mustTag ctor = do
        env <- get

        case Map.lookup ctor (leCtorTags env) of
            Just n -> pure n
            Nothing -> failLower ("Alloy.Lower: missing constructor tag for " ++ ctor)

    mustTypeConName :: Type -> Lower String
    mustTypeConName t =
        case getTypeCtorName t of
            Just nm -> pure nm
            Nothing -> failLower "Alloy.Lower: cannot determine result type constructor name for compose"

    payloadType :: String -> Lower Type
    payloadType ctor = do
        env <- get
        case Map.lookup ctor (leCtorFields env) of
            Just (t : _) -> pure t
            Just [] -> failLower ("Alloy.Lower: constructor " ++ ctor ++ " has no fields")
            Nothing -> failLower ("Alloy.Lower: missing constructor fields for " ++ ctor)
    resultProfile :: Type -> Lower (Maybe MonadProfile)
    resultProfile t = do
        env <- get
        case getTypeCtorName t of
            Just tn -> pure (lookupProfile (leProfiles env) tn)
            Nothing -> pure Nothing
    getTypeCtorName :: Type -> Maybe String
    getTypeCtorName t =
        case t of
            TApp l _ -> getTypeCtorName l
            TConstructor (TypeConstructor nm _) -> Just nm
            _ -> Nothing

buildCtorFieldMap :: MetallicModule -> Map.Map String [Type]
buildCtorFieldMap mm =
    Map.fromList
        [ (mcName c, mcFields c)
        | MAlgebraicType{mtConstructors = ctors} <- mmTypes mm
        , c <- ctors
        ]

buildCtorTagMap :: MetallicModule -> Map.Map String Integer
buildCtorTagMap mm =
    Map.fromList
        [ (mcName c, fromIntegral (mcTag c))
        | MAlgebraicType{mtConstructors = ctors} <- mmTypes mm
        , c <- ctors
        ]

getCtorTag :: String -> Lower Integer
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
                    tagOpName <- lift $ emitLetTmp intType (OpTagOf rootOp)
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
    go acc (MPanic _ _) = acc

patternHasBinder :: Pattern -> Bool
patternHasBinder (PVar _) = True
patternHasBinder (PAs _ p) = patternHasBinder p
patternHasBinder (PConstructor _ ps) = any patternHasBinder ps
patternHasBinder (PTuple ps) = any patternHasBinder ps
patternHasBinder (PArray ps) = any patternHasBinder ps
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
bindOne (PVar v) op _ = pure [(v, op)]
bindOne PWildcard _ _ = pure []
bindOne (PLit _) _ _ = pure []
bindOne (PAs v p) op vt = do
    more <- bindOne p op vt
    pure ((v, op) : more)
bindOne (PConstructor _ sub) op vt = bindPositional sub
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
                    Nothing -> failLower "Unable to infer field type for pattern binder"
                tmp <- lift $ emitLetTmp ty (OpProject op idx)
                bindOne sp (OpVar tmp) vt
            else pure []
    collectVars (PVar v) = [v]
    collectVars (PAs v p) = v : collectVars p
    collectVars (PConstructor _ ps) = concatMap collectVars ps
    collectVars (PTuple ps) = concatMap collectVars ps
    collectVars (PArray ps) = concatMap collectVars ps
    collectVars _ = []
bindOne (PTuple sub) op vt = bindOne (PConstructor "" sub) op vt
bindOne (PArray _) _ _ = pure []

withBinding :: String -> AOperand -> Lower a -> Lower a
withBinding name op action = do
    old <- get
    let newEnv = Map.insert name op (leVars old)
    put old{leVars = newEnv}
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
