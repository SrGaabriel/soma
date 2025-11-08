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
        afName,
        afParams,
        afReturnType
    ),
    AlloyModule (AlloyModule, amFunctions),
    Name,
 )
import Data.Char (isAlphaNum)
import Data.List (intercalate)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Typing.Types (
    TyConstructor (..),
    TyVar (..),
    Type (..),
    boolType,
    extractTyVars,
    intType,
    strType,
 )

monomorphizeModule :: AlloyModule -> AlloyModule
monomorphizeModule m@AlloyModule{amFunctions = baseFns} =
    let baseFnMap = toFnMap baseFns

        (allFns, instCache) = monoFixpoint baseFnMap baseFns Map.empty

        dedupedFns = dedupByName allFns
        rwMap = computeRewriteMap baseFnMap instCache dedupedFns
        finalFns = map (applyRewrites baseFnMap rwMap) dedupedFns

        -- Only emit monomorphized instances, not unused polymorphic base functions
        -- instCache maps InstKey -> specialized function name
        -- We want to keep specialized functions (those in the values of instCache)
        -- and any concrete base functions
        specializedNames = Set.fromList (Map.elems instCache)
        isSpecialized fn = afName fn `Set.member` specializedNames

        -- Keep functions that are specialized instances or concrete base functions
        concretesFns = map eliminateAllTypeVars $ filter isMonomorphized finalFns

        isMonomorphized fn =
            isSpecialized fn || not (hasTypeVars fn)

        hasTypeVars fn =
            any (hasTypeVar . snd) (afParams fn) || hasTypeVar (afReturnType fn)

        hasTypeVar ty = case ty of
            TVar _ -> True
            TApp a b -> hasTypeVar a || hasTypeVar b
            TArrow a b -> hasTypeVar a || hasTypeVar b
            _ -> False
    in m{amFunctions = concretesFns}

monomorphizeFunction :: Map String AlloyFunction -> AlloyFunction -> (AlloyFunction, [AlloyFunction])
monomorphizeFunction baseFnMap fn =
    let (allFns, instCache) = monoFixpoint baseFnMap [fn] Map.empty
        rwMap = computeRewriteMap baseFnMap instCache allFns
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

-- Deduplicate functions by name (last wins) to avoid duplicate specialized symbols
dedupByName :: [AlloyFunction] -> [AlloyFunction]
dedupByName fns = Map.elems (Map.fromList [(afName f, f) | f <- fns])

monoFixpoint ::
    Map String AlloyFunction -> -- base functions (eligible for specialization)
    [AlloyFunction] -> -- current function set (grows with clones)
    Map InstKey String -> -- instantiation cache: key -> specialized name
    ([AlloyFunction], Map InstKey String)
monoFixpoint baseFnMap fns0 cache0 =
    let reqs = scanForRequests baseFnMap fns0
        newReqs = [(b, s, k) | (b, s, k) <- reqs, Map.notMember k cache0]
        newClones =
            [ let base = fromMaybe (unknownBase b) (Map.lookup b baseFnMap)
                  clone = specializeFunction base s
              in (k, afName clone, clone)
            | (b, s, k) <- newReqs
            ]
        cache1 = foldl' (\acc (k, nm, _) -> Map.insert k nm acc) cache0 newClones
        fns1 = fns0 ++ [c | (_, _, c) <- newClones]
    in if null newClones
        then (fns0, cache0)
        else monoFixpoint baseFnMap fns1 cache1
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
        (_, reqs) = foldl' (scanBlock baseEnv) (0, []) afBlocks
    in reqs
  where
    scanBlock ::
        Map String Type ->
        (CallSiteId, [(String, TySubst, InstKey)]) ->
        ABlock ->
        (CallSiteId, [(String, TySubst, InstKey)])
    scanBlock env (cid, reqs) ABlock{abParams = blkParams, abInstrs} =
        let env0 = env `Map.union` Map.fromList blkParams
            step (cidAcc, reqsAcc, envAcc) instr =
                case instr of
                    ILet name ty op ->
                        let (cid'', reqs'') = scanOp envAcc (cidAcc, reqsAcc) op
                            env'' = Map.insert name ty envAcc
                        in (cid'', reqs'', env'')
                    IEffect _ -> (cidAcc, reqsAcc, envAcc)
            (cid', reqs', _) = foldl' step (cid, reqs, env0) abInstrs
        in (cid', reqs')

    scanOp ::
        Map String Type ->
        (CallSiteId, [(String, TySubst, InstKey)]) ->
        AOp ->
        (CallSiteId, [(String, TySubst, InstKey)])
    scanOp env (cid, reqs) (OpCall (Direct callee) args) =
        case Map.lookup callee baseFnMap of
            Nothing -> (cid + 1, reqs) -- not a monomorphizable base function
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
    scanOp _ s (OpCall (Indirect _) _) = s
    scanOp _ s _ = s

specializeFunction :: AlloyFunction -> TySubst -> AlloyFunction
specializeFunction fn subst =
    let mangledName = mangleInstance fn subst
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
    Map String AlloyFunction -> -- base functions (only these are rewritten)
    Map InstKey String -> -- inst cache (key -> specialized name)
    [AlloyFunction] -> -- functions to scan for calls
    RewriteMap
computeRewriteMap baseFnMap cache =
    foldl' goFn Map.empty
  where
    goFn :: RewriteMap -> AlloyFunction -> RewriteMap
    goFn acc AlloyFunction{afName = callerName, afParams = funParams, afBlocks} =
        let env0 = Map.fromList funParams
            (_, acc') = foldl' (goBlock env0 callerName) (0, acc) afBlocks
        in acc'

    goBlock ::
        Map String Type ->
        String ->
        (CallSiteId, RewriteMap) ->
        ABlock ->
        (CallSiteId, RewriteMap)
    goBlock env caller (cid, acc) ABlock{abParams = blkParams, abInstrs} =
        let env' = env `Map.union` Map.fromList blkParams
            step (cidAcc, accAcc, envAcc) instr =
                case instr of
                    ILet n t (OpCall (Direct callee) args) ->
                        let cid' = cidAcc + 1
                            envAcc' = Map.insert n t envAcc
                        in case Map.lookup callee baseFnMap of
                            Nothing -> (cid', accAcc, envAcc')
                            Just calleeFn ->
                                case mapM (operandType envAcc) args of
                                    Nothing -> (cid', accAcc, envAcc')
                                    Just argTys ->
                                        case matchCalleeParams (afParams calleeFn) argTys of
                                            Just subst
                                                | not (Map.null subst) && allConcreteSubst subst ->
                                                    let key = instKey calleeFn subst
                                                    in case Map.lookup key cache of
                                                        Just specializedName ->
                                                            let acc' = Map.insert (caller, cidAcc) specializedName accAcc
                                                            in (cid', acc', envAcc')
                                                        Nothing -> (cid', accAcc, envAcc')
                                            _ -> (cid', accAcc, envAcc')
                    ILet n t _ ->
                        (cidAcc, accAcc, Map.insert n t envAcc)
                    IEffect _ ->
                        (cidAcc, accAcc, envAcc)
            (cid'', acc'', _) = foldl' step (cid, acc, env') abInstrs
        in (cid'', acc'')

applyRewrites :: Map String AlloyFunction -> RewriteMap -> AlloyFunction -> AlloyFunction
applyRewrites baseFnMap rwMap fn@AlloyFunction{afName = callerName, afBlocks, afParams = funParams} =
    let env0 = Map.fromList funParams
        (_, blocks') = foldl' (rewriteBlock env0) (0, []) afBlocks
    in fn{afBlocks = reverse blocks'}
  where
    rewriteBlock :: Map String Type -> (CallSiteId, [ABlock]) -> ABlock -> (CallSiteId, [ABlock])
    rewriteBlock env (cid, acc) blk@ABlock{abInstrs, abParams = blkParams} =
        let env' = env `Map.union` Map.fromList blkParams
            (cid', instrs', _) = foldl' rewriteInstr (cid, [], env') abInstrs
        in ( cid'
           , ABlock
                { abName = abName blk
                , abParams = abParams blk
                , abInstrs = reverse instrs'
                , abTerminator = abTerminator blk
                }
                : acc
           )

    rewriteInstr :: (CallSiteId, [AInstr], Map String Type) -> AInstr -> (CallSiteId, [AInstr], Map String Type)
    rewriteInstr (cid, acc, env) (ILet n t (OpCall (Direct callee) args)) =
        let key = (callerName, cid)
            -- First try rewrite map (monomorphized functions)
            callee' = Map.findWithDefault callee key rwMap
            -- Then try trait method resolution
            callee'' = resolveTraitMethod env callee' args
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
        in (cid + 1, ILet n t' (OpCall (Direct callee'') args) : acc, Map.insert n t' env)
    rewriteInstr (cid, acc, env) (ILet n t op) =
        let t' = specializeTypeFromEnv env t
            op' = specializeOpTypes env op t'
        in (cid, ILet n t' op' : acc, Map.insert n t' env)
    rewriteInstr (cid, acc, env) instr = (cid, instr : acc, env)

    -- Resolve trait method calls to instance implementations
    -- e.g., equals(x: Optional, y: Optional) -> equals$Optional(x, y)
    resolveTraitMethod :: Map String Type -> String -> [AOperand] -> String
    resolveTraitMethod env methodName args
        -- Check if this is a trait method call (not in baseFnMap but has a typed instance variant)
        | Nothing <- Map.lookup methodName baseFnMap =
            case mapM (operandType env) args of
                Just (firstArgType : _rest) ->
                    -- Try to find an instance implementation for the first argument's type
                    let typeName = extractTypeName firstArgType
                        instanceMethodName = methodName ++ "$" ++ typeName
                    in if Map.member instanceMethodName baseFnMap
                        then instanceMethodName
                        else methodName
                _ -> methodName
        | otherwise = methodName
      where
        extractTypeName :: Type -> String
        extractTypeName (TConstructor (TypeConstructor name _)) = name
        extractTypeName (TApp _ ty) = extractTypeName ty
        extractTypeName _ = "Unknown"

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
    in fn{afParams = params', afReturnType = ret', afBlocks = blocks'}

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

mangleInstance :: AlloyFunction -> TySubst -> String
mangleInstance AlloyFunction{afName = base, afParams = ps, afReturnType = ret} subst =
    let tyvars = extractTyVars (foldr (TArrow . snd) ret ps)
        concreteArgs = [applySubst subst (TVar tv) | tv <- tyvars]
        enc = intercalate "_" (map encodeType concreteArgs)
    in if null concreteArgs then base else base ++ "$" ++ enc

encodeType :: Type -> String
encodeType t =
    case t of
        TVar (TypeVar v _) -> "v_" ++ sanitize v
        TSkolem _ -> "sk"
        TConstructor c -> sanitize (tcName c)
        TApp a b -> encodeType a ++ "_" ++ encodeType b
        TArrow a b -> "fn_" ++ encodeType a ++ "_to_" ++ encodeType b
        TUnresolved s -> "u_" ++ sanitize s
  where
    sanitize :: String -> String
    sanitize = map (\c -> if isAlphaNum c then c else '_')
