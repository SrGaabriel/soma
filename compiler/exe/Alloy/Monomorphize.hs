{-# LANGUAGE NamedFieldPuns #-}

module Alloy.Monomorphize (
    monomorphizeModule,
    monomorphizeFunction,
    InstKey (..),
    TySubst,
) where

import Alloy.Ir (
    ABlock (..),
    ACallable (..),
    AConst (CBool, CInt, CString, CUnit),
    AEffect,
    AInstr (..),
    AOp (
        OpAllocHeap,
        OpAllocStack,
        OpBin,
        OpCall,
        OpCmp,
        OpConstruct,
        OpDictCall,
        OpGetDict,
        OpIndex,
        OpLoad,
        OpMakeArray,
        OpMakeTuple,
        OpProject,
        OpTagOf,
        OpUnary
    ),
    AOperand (..),
    ATerminator (..),
    AlloyFunction (
        AlloyFunction,
        afBlocks,
        afConstraints,
        afName,
        afParams,
        afReturnType
    ),
    AlloyModule (AlloyModule, amFunctions, amName),
    Name,
 )
import Alloy.Naming (
    extractBaseTypeName,
    extractTypeName,
    makeInstanceMethodName,
    makeMonomorphicName,
 )
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Typing.Types (
    TyVar (..),
    Type (..),
    boolType,
    extractTyVars,
    intType,
    strType,
 )

monomorphizeModule :: AlloyModule -> AlloyModule
monomorphizeModule m@AlloyModule{amName = moduleName, amFunctions = funcs} =
    let baseFnMap = toFnMap funcs
        (allFns, instCache) = monoFixpoint moduleName baseFnMap funcs Map.empty
        dedupedFns = dedupByName allFns
        rwMap = computeRewriteMap moduleName baseFnMap instCache dedupedFns
        finalFns = map (applyRewrites baseFnMap rwMap) dedupedFns
        _baseNames = Set.fromList (map afName funcs)
        specializedNames = Set.fromList (Map.elems instCache)
        isKept = isMonomorphized specializedNames
        isMonomorphized specNames fn =
            afName fn `Set.member` specNames || not (hasTypeVars fn)
        hasTypeVars fn =
            any (hasTypeVar . snd) (afParams fn) || hasTypeVar (afReturnType fn)
        hasTypeVar ty = case ty of
            TVar _ -> True
            TApp a b -> hasTypeVar a || hasTypeVar b
            TArrow a b -> hasTypeVar a || hasTypeVar b
            _ -> False
        concretesFns = map eliminateAllTypeVars $ filter isKept finalFns
    in m{amFunctions = concretesFns}

monomorphizeFunction :: String -> Map String AlloyFunction -> AlloyFunction -> (AlloyFunction, [AlloyFunction])
monomorphizeFunction moduleName baseFnMap fn =
    let (allFns, instCache) = monoFixpoint moduleName baseFnMap [fn] Map.empty
        rwMap = computeRewriteMap moduleName baseFnMap instCache allFns
        rewrittenAll = map (applyRewrites baseFnMap rwMap) allFns
        concreteAll = map eliminateAllTypeVars rewrittenAll
    in case concreteAll of
        [] -> (fn, [])
        (f : cs) -> (f, cs)

type TySubst = Map TyVar Type

data InstKey = InstKey
    { ikBase :: String
    , ikArgs :: [Type]
    }
    deriving (Eq, Ord, Show)

type CallSiteId = Int

type RewriteMap = Map (String, CallSiteId) String

toFnMap :: [AlloyFunction] -> Map String AlloyFunction
toFnMap = Map.fromList . map (\f -> (afName f, f))

dedupByName :: [AlloyFunction] -> [AlloyFunction]
dedupByName fns = Map.elems (Map.fromList [(afName f, f) | f <- fns])

monoFixpoint ::
    String ->
    Map String AlloyFunction ->
    [AlloyFunction] ->
    Map InstKey String ->
    ([AlloyFunction], Map InstKey String)
monoFixpoint moduleName baseFnMap fns0 cache0 =
    let reqs = scanForRequests baseFnMap fns0
        newReqs = [(b, s, k) | (b, s, k) <- reqs, Map.notMember k cache0]
        newClones =
            [ let base = fromMaybe (unknownBase b) (Map.lookup b baseFnMap)
                  clone = specializeFunction moduleName base s
              in (k, afName clone, clone)
            | (b, s, k) <- newReqs
            ]
        cache1 = foldl' (\acc (k, nm, _) -> Map.insert k nm acc) cache0 newClones
        fns1 = fns0 ++ [c | (_, _, c) <- newClones]
    in if null newClones
        then (fns0, cache0)
        else monoFixpoint moduleName baseFnMap fns1 cache1
  where
    unknownBase n = error ("Alloy.Monomorphize: unknown base function " ++ n)

scanForRequests ::
    Map String AlloyFunction ->
    [AlloyFunction] ->
    [(String, TySubst, InstKey)]
scanForRequests baseFnMap = concatMap (scanCallsInFunction baseFnMap)

scanCallsInFunction ::
    Map String AlloyFunction ->
    AlloyFunction ->
    [(String, TySubst, InstKey)]
scanCallsInFunction baseFnMap AlloyFunction{afParams = funParams, afBlocks} =
    let baseEnv = Map.fromList funParams
        allInstrs = concatMap abInstrs afBlocks
        fullEnv = foldl' addInstrToEnv baseEnv allInstrs
        (_, reqs) = foldl' (scanBlock fullEnv) (0, []) afBlocks
    in reqs
  where
    addInstrToEnv :: Map String Type -> AInstr -> Map String Type
    addInstrToEnv env (ILet name ty _) = Map.insert name ty env
    addInstrToEnv env (IEffect _) = env
    scanBlock ::
        Map String Type ->
        (CallSiteId, [(String, TySubst, InstKey)]) ->
        ABlock ->
        (CallSiteId, [(String, TySubst, InstKey)])
    scanBlock env (cid, reqs) ABlock{abParams = blkParams, abInstrs} =
        let env0 = env `Map.union` Map.fromList blkParams
            step (cidAcc, reqsAcc) instr =
                case instr of
                    ILet _name _ty op ->
                        let (cid'', reqs'') = scanOp env0 (cidAcc, reqsAcc) op
                        in (cid'', reqs'')
                    IEffect _ -> (cidAcc, reqsAcc)
            (cid', reqs') = foldl' step (cid, reqs) abInstrs
        in (cid', reqs')
    scanOp ::
        Map String Type ->
        (CallSiteId, [(String, TySubst, InstKey)]) ->
        AOp ->
        (CallSiteId, [(String, TySubst, InstKey)])
    scanOp env (cid, reqs) (OpCall (Direct callee) args) =
        let resolvedCallee = resolveTraitMethod baseFnMap env callee args
            result = case Map.lookup resolvedCallee baseFnMap of
                Nothing -> (cid + 1, reqs)
                Just calleeFn ->
                    case mapM (operandType env) args of
                        Nothing -> (cid + 1, reqs)
                        Just argTys ->
                            case matchCalleeParams (afParams calleeFn) argTys of
                                Just subst
                                    | not (Map.null subst) && allConcreteSubst subst ->
                                        let k = instKey calleeFn subst
                                        in (cid + 1, (afName calleeFn, subst, k) : reqs)
                                    | not (Map.null subst) -> (cid + 1, reqs)
                                Just _ -> (cid + 1, reqs)
                                Nothing -> (cid + 1, reqs)
        in result
    scanOp _ s (OpCall (Indirect _) _) = s
    scanOp env (cid, reqs) (OpDictCall _dict _idx methodName args) =
        let resolvedMethod = resolveTraitMethod baseFnMap env methodName args
        in case Map.lookup resolvedMethod baseFnMap of
            Nothing -> (cid + 1, reqs)
            Just calleeFn ->
                case mapM (operandType env) args of
                    Nothing -> (cid + 1, reqs)
                    Just argTys ->
                        case matchCalleeParams (afParams calleeFn) argTys of
                            Just subst
                                | not (Map.null subst) && allConcreteSubst subst ->
                                    let k = instKey calleeFn subst
                                    in (cid + 1, (afName calleeFn, subst, k) : reqs)
                            _ -> (cid + 1, reqs)
    scanOp _ s _ = s

resolveTraitMethod :: Map String AlloyFunction -> Map String Type -> String -> [AOperand] -> String
resolveTraitMethod baseFnMap env methodName args
    | Nothing <- Map.lookup methodName baseFnMap =
        case mapM (operandType env) args of
            Just (firstArgType : _rest) ->
                let typeName = extractTypeName firstArgType
                    instanceMethodName = makeInstanceMethodName methodName typeName
                in if Map.member instanceMethodName baseFnMap
                    then instanceMethodName
                    else
                        let baseTypeName = extractBaseTypeName firstArgType
                            polyInstanceName = makeInstanceMethodName methodName baseTypeName
                        in if Map.member polyInstanceName baseFnMap
                            then polyInstanceName
                            else methodName
            _ -> methodName
    | otherwise = methodName

specializeFunction :: String -> AlloyFunction -> TySubst -> AlloyFunction
specializeFunction moduleName fn subst =
    let mangledName = mangleInstance moduleName fn subst
        params' = [(n, applySubst subst t) | (n, t) <- afParams fn]
        ret' = applySubst subst (afReturnType fn)
        blocks' = map (specializeBlock subst) (afBlocks fn)
    in fn{afName = mangledName, afParams = params', afReturnType = ret', afBlocks = blocks'}

specializeBlock :: TySubst -> ABlock -> ABlock
specializeBlock subst b@ABlock{abParams, abInstrs, abTerminator} =
    let params' = [(n, applySubst subst t) | (n, t) <- abParams]
        instrs' = map (specializeInstr subst) abInstrs
        term' = specializeTerm abTerminator
    in b{abParams = params', abInstrs = instrs', abTerminator = term'}

specializeInstr :: TySubst -> AInstr -> AInstr
specializeInstr subst (ILet n t op) = ILet n (applySubst subst t) (specializeOp subst op)
specializeInstr subst (IEffect eff) = IEffect (specializeEffect subst eff)

specializeEffect :: TySubst -> AEffect -> AEffect
specializeEffect _ eff = eff

specializeOp :: TySubst -> AOp -> AOp
specializeOp subst op =
    case op of
        OpBin k a b -> OpBin k a b
        OpUnary k a -> OpUnary k a
        OpCmp k a b -> OpCmp k a b
        OpLoad a -> OpLoad a
        OpAllocStack ty -> OpAllocStack (applySubst subst ty)
        OpAllocHeap ty -> OpAllocHeap (applySubst subst ty)
        OpCall c args -> OpCall (specializeCallable c) args
        OpConstruct tn tag fields -> OpConstruct tn tag fields
        OpTagOf a -> OpTagOf a
        OpProject a i -> OpProject a i
        OpIndex a i -> OpIndex a i
        OpMakeArray xs -> OpMakeArray xs
        OpMakeTuple xs -> OpMakeTuple xs
        OpGetDict className ty -> OpGetDict className ty
        OpDictCall dict methodIdx method args -> OpDictCall dict methodIdx method args

specializeCallable :: ACallable -> ACallable
specializeCallable (Direct name) = Direct name
specializeCallable (Indirect a) = Indirect a

specializeTerm :: ATerminator -> ATerminator
specializeTerm term =
    case term of
        ABr b args -> ABr b args
        ACondBr c tb ta fb fa -> ACondBr c tb ta fb fa
        ASwitch v cases mdef -> ASwitch v cases mdef
        ARet mv -> ARet mv
        AUnreachable -> AUnreachable

computeRewriteMap ::
    String ->
    Map String AlloyFunction ->
    Map InstKey String ->
    [AlloyFunction] ->
    RewriteMap
computeRewriteMap _moduleName baseFnMap cache =
    foldl' goFn Map.empty
  where
    goFn :: RewriteMap -> AlloyFunction -> RewriteMap
    goFn acc AlloyFunction{afName = callerName, afParams = funParams, afBlocks} =
        let env0 = Map.fromList funParams
            allInstrs = concatMap abInstrs afBlocks
            fullEnv = foldl' addInstrToEnv env0 allInstrs
            (_, acc') = foldl' (goBlock fullEnv callerName) (0, acc) afBlocks
        in acc'
    addInstrToEnv :: Map String Type -> AInstr -> Map String Type
    addInstrToEnv env (ILet name ty _) = Map.insert name ty env
    addInstrToEnv env (IEffect _) = env
    goBlock ::
        Map String Type ->
        String ->
        (CallSiteId, RewriteMap) ->
        ABlock ->
        (CallSiteId, RewriteMap)
    goBlock env caller (cid, acc) ABlock{abParams = blkParams, abInstrs} =
        let env' = env `Map.union` Map.fromList blkParams
            step (cidAcc, accAcc) instr =
                case instr of
                    ILet _n _t (OpCall (Direct callee) args) ->
                        let cid' = cidAcc + 1
                            resolvedCallee = resolveTraitMethod baseFnMap env' callee args
                        in case Map.lookup resolvedCallee baseFnMap of
                            Nothing -> (cid', accAcc)
                            Just calleeFn ->
                                case mapM (operandType env') args of
                                    Nothing -> (cid', accAcc)
                                    Just argTys ->
                                        case matchCalleeParams (afParams calleeFn) argTys of
                                            Just subst
                                                | not (Map.null subst) && allConcreteSubst subst ->
                                                    let key = instKey calleeFn subst
                                                    in case Map.lookup key cache of
                                                        Just specializedName ->
                                                            let acc' = Map.insert (caller, cidAcc) specializedName accAcc
                                                            in (cid', acc')
                                                        Nothing -> (cid', accAcc)
                                            _ -> (cid', accAcc)
                    _ -> (cidAcc, accAcc)
            (cid'', acc'') = foldl' step (cid, acc) abInstrs
        in (cid'', acc'')

applyRewrites :: Map String AlloyFunction -> RewriteMap -> AlloyFunction -> AlloyFunction
applyRewrites baseFnMap rwMap fn@AlloyFunction{afName = callerName, afBlocks, afParams = funParams} =
    let env0 = Map.fromList funParams
        allInstrs = concatMap abInstrs afBlocks
        fullEnv = foldl' addInstrToEnv env0 allInstrs
        (_, blocks') = foldl' (rewriteBlock fullEnv) (0, []) afBlocks
    in fn{afBlocks = reverse blocks'}
  where
    addInstrToEnv :: Map String Type -> AInstr -> Map String Type
    addInstrToEnv env (ILet name ty _) = Map.insert name ty env
    addInstrToEnv env (IEffect _) = env
    rewriteBlock :: Map String Type -> (CallSiteId, [ABlock]) -> ABlock -> (CallSiteId, [ABlock])
    rewriteBlock env (cid, acc) blk@ABlock{abInstrs, abParams = blkParams} =
        let env' = env `Map.union` Map.fromList blkParams
            (cid', instrs') = foldl' (rewriteInstr env') (cid, []) abInstrs
        in ( cid'
           , ABlock
                { abName = abName blk
                , abParams = abParams blk
                , abInstrs = reverse instrs'
                , abTerminator = abTerminator blk
                }
                : acc
           )
    rewriteInstr :: Map String Type -> (CallSiteId, [AInstr]) -> AInstr -> (CallSiteId, [AInstr])
    rewriteInstr env (cid, acc) (ILet n t (OpCall (Direct callee) args)) =
        let key = (callerName, cid)
            callee' = Map.findWithDefault callee key rwMap
            callee'' = resolveTraitMethod baseFnMap env callee' args
            t' = case Map.lookup callee'' baseFnMap of
                Just calleeFn | callee' /= callee || callee'' /= callee ->
                    case mapM (operandType env) args of
                        Just argTys ->
                            case matchCalleeParams (afParams calleeFn) argTys of
                                Just subst
                                    | not (Map.null subst) && allConcreteSubst subst ->
                                        let retTy = afReturnType calleeFn
                                        in applySubst subst retTy
                                _ -> t
                        _ -> t
                _ -> t
        in (cid + 1, ILet n t' (OpCall (Direct callee'') args) : acc)
    rewriteInstr env (cid, acc) (ILet n t op) =
        let t' = specializeTypeFromEnv env t
            op' = specializeOpTypes env op t'
        in (cid, ILet n t' op' : acc)
    rewriteInstr _ (cid, acc) instr = (cid, instr : acc)
    specializeOpTypes :: Map String Type -> AOp -> Type -> AOp
    specializeOpTypes env op _resultTy =
        case op of
            OpAllocStack ty -> OpAllocStack (specializeTypeFromEnv env ty)
            OpAllocHeap ty -> OpAllocHeap (specializeTypeFromEnv env ty)
            _ -> op
    specializeTypeFromEnv :: Map String Type -> Type -> Type
    specializeTypeFromEnv _ = eliminateTypeVarsWithDefaults

operandType :: Map String Type -> AOperand -> Maybe Type
operandType env (OpVar n) = Map.lookup n env
operandType _ (OpConst c) =
    case c of
        CInt _ -> Just intType
        CBool _ -> Just boolType
        CString _ -> Just strType
        CUnit -> Nothing

matchCalleeParams :: [(Name, Type)] -> [Type] -> Maybe TySubst
matchCalleeParams formals actuals
    | length formals /= length actuals = Nothing
    | otherwise = foldl' step (Just Map.empty) (zip (map snd formals) actuals)
  where
    step :: Maybe TySubst -> (Type, Type) -> Maybe TySubst
    step Nothing _ = Nothing
    step (Just subst) (polyT, concT) =
        fmap (mergeSubst subst) (matchTypes subst polyT concT)

matchTypes :: TySubst -> Type -> Type -> Maybe TySubst
matchTypes subst poly conc =
    case applySubst subst poly of
        TVar tv -> Just (Map.insert tv conc subst)
        TApp l1 r1 ->
            case conc of
                TApp l2 r2 -> do
                    s1 <- matchTypes subst l1 l2
                    matchTypes s1 r1 r2
                _ -> Nothing
        TArrow a1 b1 ->
            case conc of
                TArrow a2 b2 -> do
                    s1 <- matchTypes subst a1 a2
                    matchTypes s1 b1 b2
                _ -> Nothing
        t@(TConstructor _) -> if t == conc then Just subst else Nothing
        t@(TSkolem _) -> if t == conc then Just subst else Nothing
        TUnresolved _ -> Just subst

mergeSubst :: TySubst -> TySubst -> TySubst
mergeSubst = Map.union

applySubst :: TySubst -> Type -> Type
applySubst s t =
    case t of
        TVar tv -> Map.findWithDefault t tv s
        TApp a b -> TApp (applySubst s a) (applySubst s b)
        TArrow a b -> TArrow (applySubst s a) (applySubst s b)
        _ -> t

eliminateAllTypeVars :: AlloyFunction -> AlloyFunction
eliminateAllTypeVars fn@AlloyFunction{afParams, afReturnType, afBlocks} =
    let params' = [(n, eliminateTypeVarsWithDefaults t) | (n, t) <- afParams]
        ret' = eliminateTypeVarsWithDefaults afReturnType
        blocks' = map eliminateTypeVarsBlock afBlocks
    in fn{afParams = params', afReturnType = ret', afBlocks = blocks', afConstraints = []}

eliminateTypeVarsBlock :: ABlock -> ABlock
eliminateTypeVarsBlock b@ABlock{abParams, abInstrs} =
    let params' = [(n, eliminateTypeVarsWithDefaults t) | (n, t) <- abParams]
        instrs' = map eliminateTypeVarsInstr abInstrs
    in b{abParams = params', abInstrs = instrs'}

eliminateTypeVarsInstr :: AInstr -> AInstr
eliminateTypeVarsInstr (ILet n t op) =
    ILet n (eliminateTypeVarsWithDefaults t) (eliminateTypeVarsOp op)
eliminateTypeVarsInstr eff = eff

eliminateTypeVarsOp :: AOp -> AOp
eliminateTypeVarsOp op =
    case op of
        OpAllocStack ty -> OpAllocStack (eliminateTypeVarsWithDefaults ty)
        OpAllocHeap ty -> OpAllocHeap (eliminateTypeVarsWithDefaults ty)
        _ -> op

eliminateTypeVarsWithDefaults :: Type -> Type
eliminateTypeVarsWithDefaults ty =
    case ty of
        TVar _ -> intType
        TApp a b -> TApp (eliminateTypeVarsWithDefaults a) (eliminateTypeVarsWithDefaults b)
        TArrow a b -> TArrow (eliminateTypeVarsWithDefaults a) (eliminateTypeVarsWithDefaults b)
        _ -> ty

allConcreteSubst :: TySubst -> Bool
allConcreteSubst = all isConcreteType . Map.elems

isConcreteType :: Type -> Bool
isConcreteType (TVar _) = False
isConcreteType (TSkolem _) = True
isConcreteType (TConstructor _) = True
isConcreteType (TApp a b) = isConcreteType a && isConcreteType b
isConcreteType (TArrow a b) = isConcreteType a && isConcreteType b
isConcreteType (TUnresolved _) = False

functionTyVars :: AlloyFunction -> [TyVar]
functionTyVars AlloyFunction{afParams = ps, afReturnType = ret} =
    extractTyVars (foldr (TArrow . snd) ret ps)

instKey :: AlloyFunction -> TySubst -> InstKey
instKey fn subst =
    let tvs = functionTyVars fn
        args = [applySubst subst (TVar tv) | tv <- tvs]
    in InstKey (afName fn) args

mangleInstance :: String -> AlloyFunction -> TySubst -> String
mangleInstance moduleName AlloyFunction{afName = base, afParams = ps, afReturnType = ret} subst =
    let tyvars = extractTyVars (foldr (TArrow . snd) ret ps)
        concreteArgs = [applySubst subst (TVar tv) | tv <- tyvars]
    in makeMonomorphicName moduleName base concreteArgs
