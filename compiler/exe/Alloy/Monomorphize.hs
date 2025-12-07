{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Alloy.Monomorphize (
    monomorphizeModule,
    monomorphizeFunction,
    InstKey (..),
    TySubst,
) where

import Alloy.Ir (
    ABlock (..),
    ACallable (..),
    AConst (..),
    AEffect (..),
    AInstr (..),
    AOp (..),
    AOperand (..),
    AlloyFunction (..),
    AlloyModule (..),
 )
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, listToMaybe)
import qualified Data.Set as Set
import Project.Name (Name, makeMonomorphized, nameBaseUnique, nameToString)
import qualified Project.Name as PN
import Project.Unique (Unique)
import Typing.Types (
    SkolemVar (..),
    TyConstructor (..),
    TyVar (..),
    Type (..),
    boolType,
    intType,
    strType,
    unitType,
 )

type TySubst = Map TyVar Type

data InstKey = InstKey
    { ikBase :: Name
    , ikArgs :: [Type]
    }
    deriving (Eq, Ord, Show)

type CallSiteId = Int

type RewriteMap = Map (Name, CallSiteId) Name

monomorphizeModule :: AlloyModule -> AlloyModule
monomorphizeModule m@AlloyModule{amName = moduleName, amFunctions = funcs} =
    let baseFnMap = toFnMap funcs

        -- Phase 1: Fixpoint Scan
        (allFns, instCache) = monoFixpoint moduleName baseFnMap funcs Map.empty
        dedupedFns = dedupByName allFns

        -- Phase 2: Rewrite
        rwMap = computeRewriteMap baseFnMap instCache dedupedFns

        -- Apply rewrites
        rewrittenFns = map (applyRewrites rwMap instCache baseFnMap) dedupedFns

        -- Phase 3: Cleanup
        specializedNames = Set.fromList (Map.elems instCache)
        -- Keep instance methods even if polymorphic, as they might be needed by other modules
        isKept fn =
            afName fn `Set.member` specializedNames
                || nameToString (afName fn) == "main"
                || not (hasTypeVars fn)

        finalFns = map eliminateAllTypeVars $ filter isKept rewrittenFns
    in m{amFunctions = finalFns}

monomorphizeFunction :: String -> Map Name AlloyFunction -> AlloyFunction -> (AlloyFunction, [AlloyFunction])
monomorphizeFunction moduleName baseFnMap fn =
    let (allFns, instCache) = monoFixpoint moduleName baseFnMap [fn] Map.empty
        rwMap = computeRewriteMap baseFnMap instCache allFns
        rewrittenAll = map (applyRewrites rwMap instCache baseFnMap) allFns
        concreteAll = map eliminateAllTypeVars rewrittenAll
    in case concreteAll of
        [] -> (fn, [])
        (f : cs) -> (f, cs)

data CallResolution = CallResolution
    { crTargetFn :: AlloyFunction
    , crSubst :: TySubst
    , crKey :: InstKey
    }

resolveCallTarget :: Map Name AlloyFunction -> Map Name Type -> AOp -> Maybe CallResolution
resolveCallTarget baseFnMap env op =
    case op of
        OpCall (Direct calleeName) args -> resolveWithTraitLookup calleeName args
        OpDictCall _ _ methodName args -> resolveWithTraitLookup methodName args
        _ -> Nothing
  where
    resolveWithTraitLookup methodName args =
        -- First try to resolve as a trait method (instance method lookup)
        let resolvedName = resolveTraitMethod baseFnMap env methodName args
        in case resolvedName of
            Just name -> resolveCommon name args
            Nothing -> resolveCommon methodName args -- Fallback to original name
    resolveCommon name args =
        case Map.lookup name baseFnMap of
            Nothing -> Nothing
            Just calleeFn ->
                case mapM (operandType baseFnMap env) args of
                    Nothing -> Nothing
                    Just argTys ->
                        case matchCalleeParams (afParams calleeFn) argTys of
                            Just subst
                                | not (Map.null subst) && allConcreteSubst subst ->
                                    Just
                                        CallResolution
                                            { crTargetFn = calleeFn
                                            , crSubst = subst
                                            , crKey = InstKey (fnName calleeFn) (map (substType subst . snd) (afParams calleeFn))
                                            }
                            _ -> Nothing

resolveTraitMethod :: Map Name AlloyFunction -> Map Name Type -> Name -> [AOperand] -> Maybe Name
resolveTraitMethod baseFnMap env methodName args =
    case PN.nameBaseUnique methodName of
        Nothing ->
            -- Not a user name, check if it's directly in the map
            if Map.member methodName baseFnMap
                then Just methodName
                else Nothing
        Just baseUnique ->
            -- Try to find an instance method for the first argument's type
            case mapM (operandType baseFnMap env) args of
                Nothing -> Just methodName
                Just argTys ->
                    let firstNonFunctionType = case argTys of
                            (TArrow _ _ : rest) -> listToMaybe rest
                            (ty : _) -> Just ty
                            [] -> Nothing
                    in case firstNonFunctionType of
                        Nothing -> Just methodName
                        Just instanceType ->
                            -- Look for an instance method with this base and type
                            case findInstanceMethod baseUnique instanceType baseFnMap of
                                Just instanceMethodName -> Just instanceMethodName
                                Nothing -> Just methodName -- Fall back to base method

findInstanceMethod :: Unique -> Type -> Map Name AlloyFunction -> Maybe Name
findInstanceMethod baseUnique instanceType fnMap =
    let allNames = Map.keys fnMap
    in listToMaybe
        [ name
        | name <- allNames
        , PN.isInstanceMethodFor baseUnique name
        , case PN.getInstanceMethodType name of
            Just ty -> typesMatch ty instanceType
            Nothing -> False
        ]

typesMatch :: Type -> Type -> Bool
typesMatch (TVar _) _ = True
typesMatch (TConstructor tc1) (TConstructor tc2) = tcId tc1 == tcId tc2
typesMatch (TApp t1 _) t2@TConstructor{} = typesMatch t1 t2
typesMatch t1@TConstructor{} (TApp t2 _) = typesMatch t1 t2
typesMatch (TApp t1a t1b) (TApp t2a t2b) = typesMatch t1a t2a && typesMatch t1b t2b
typesMatch t1 t2 = t1 == t2

monoFixpoint ::
    String ->
    Map Name AlloyFunction ->
    [AlloyFunction] ->
    Map InstKey Name ->
    ([AlloyFunction], Map InstKey Name)
monoFixpoint moduleName baseFnMap fns0 cache0 =
    let reqs = scanForRequests baseFnMap fns0
        newReqs = [(b, s, k) | (b, s, k) <- reqs, Map.notMember k cache0]

        newClones =
            [ let baseFn = fromMaybe (error $ "Missing base fn: " ++ nameToString b) (Map.lookup b baseFnMap)
                  clone = specializeFunction moduleName baseFn s
              in (k, fnName clone, clone)
            | (b, s, k) <- newReqs
            ]

        cache1 = foldl' (\acc (k, nm, _) -> Map.insert k nm acc) cache0 newClones
        fns1 = fns0 ++ [c | (_, _, c) <- newClones]
    in if null newClones
        then (fns0, cache0)
        else monoFixpoint moduleName baseFnMap fns1 cache1

scanForRequests :: Map Name AlloyFunction -> [AlloyFunction] -> [(Name, TySubst, InstKey)]
scanForRequests baseFnMap = concatMap (scanCallsInFunction baseFnMap)

scanCallsInFunction :: Map Name AlloyFunction -> AlloyFunction -> [(Name, TySubst, InstKey)]
scanCallsInFunction baseFnMap AlloyFunction{afParams = fnParams, afBlocks} =
    let baseEnv = Map.fromList [(n, t) | (n, t) <- fnParams]
        (_, reqs) = foldl' scanBlock (baseEnv, []) afBlocks
    in reqs
  where
    scanBlock (env, reqs) ABlock{abParams, abInstrs} =
        let env' = env `Map.union` Map.fromList [(n, t) | (n, t) <- abParams]
            step (currEnv, currReqs) instr =
                case instr of
                    ILet name ty op ->
                        let callReqs = case resolveCallTarget baseFnMap currEnv op of
                                Just CallResolution{crTargetFn, crSubst, crKey} ->
                                    (fnName crTargetFn, crSubst, crKey) : currReqs
                                Nothing -> currReqs
                            -- Also check for closure allocations that reference polymorphic lambdas
                            closureReqs = case op of
                                OpAllocClosure (OpVar lambdaName) _ _ ->
                                    case Map.lookup lambdaName baseFnMap of
                                        Just lambdaFn ->
                                            case matchClosureType (afParams lambdaFn) ty of
                                                Just subst
                                                    | not (Map.null subst) && allConcreteSubst subst ->
                                                        let key = InstKey lambdaName (map (substType subst . snd) (afParams lambdaFn))
                                                        in (lambdaName, subst, key) : callReqs
                                                _ -> callReqs
                                        Nothing -> callReqs
                                _ -> callReqs
                        in (Map.insert name ty currEnv, closureReqs)
                    IEffect _ -> (currEnv, currReqs)
        in foldl' step (env', reqs) abInstrs

    matchClosureType :: [(Name, Type)] -> Type -> Maybe TySubst
    matchClosureType lambdaParams closureTy =
        let lambdaParamTypes = map snd (drop 1 lambdaParams)
        in matchFunctionParams lambdaParamTypes closureTy

    matchFunctionParams :: [Type] -> Type -> Maybe TySubst
    matchFunctionParams [] _ = Just Map.empty
    matchFunctionParams (p : ps) (TArrow argTy retTy) = do
        s1 <- unifyOne p argTy
        let ps' = map (substType s1) ps
        s2 <- matchFunctionParams ps' retTy
        Just (Map.union s2 s1)
    matchFunctionParams _ _ = Nothing

computeRewriteMap ::
    Map Name AlloyFunction ->
    Map InstKey Name ->
    [AlloyFunction] ->
    RewriteMap
computeRewriteMap baseFnMap instCache fns =
    Map.fromList $ concatMap processFn fns
  where
    processFn AlloyFunction{afName, afParams, afBlocks} =
        let baseEnv = Map.fromList [(n, t) | (n, t) <- afParams]
            -- outer fold: accumulates (CallSiteId, Rewrites) across blocks
            (_, rewrites) = foldl' (processBlock baseEnv) (0, []) afBlocks
        in map (\(cid, target) -> ((afName, cid), target)) rewrites

    processBlock baseEnv (startCid, startAcc) ABlock{abParams, abInstrs} =
        let
            blockEnv = baseEnv `Map.union` Map.fromList [(n, t) | (n, t) <- abParams]

            -- we thread the environment strictly within the block, but pass Cid/Rewrites through
            initialState = (blockEnv, startCid, startAcc)

            step (env, cid, acc) instr =
                case instr of
                    ILet name ty op ->
                        let (nextCid, hit) = case resolveCallTarget baseFnMap env op of
                                Just CallResolution{crKey} ->
                                    case Map.lookup crKey instCache of
                                        Just specName -> (cid + 1, Just specName)
                                        Nothing -> (cid + 1, Nothing)
                                Nothing ->
                                    -- Check if trait method was resolved to instance method
                                    case op of
                                        OpCall (Direct calleeName) args
                                            | Map.notMember calleeName baseFnMap ->
                                                case resolveTraitMethod baseFnMap env calleeName args of
                                                    Just resolved
                                                        | resolved /= calleeName && Map.member resolved baseFnMap ->
                                                            (cid + 1, Just resolved)
                                                    _ -> (if isCallOp op then cid + 1 else cid, Nothing)
                                        OpDictCall _ _ methodName args ->
                                            case resolveTraitMethod baseFnMap env methodName args of
                                                Just resolved
                                                    | Map.member resolved baseFnMap ->
                                                        (cid + 1, Just resolved)
                                                _ -> (if isCallOp op then cid + 1 else cid, Nothing)
                                        _ -> (if isCallOp op then cid + 1 else cid, Nothing)

                            nextAcc = case hit of
                                Just target -> (cid, target) : acc
                                Nothing -> acc

                            nextEnv = Map.insert name ty env
                        in (nextEnv, nextCid, nextAcc)
                    IEffect _ -> (env, cid, acc)

            (_, finalCid, finalAcc) = foldl' step initialState abInstrs
        in
            (finalCid, finalAcc)

    isCallOp (OpCall _ _) = True
    isCallOp (OpDictCall{}) = True
    isCallOp _ = False

applyRewrites :: RewriteMap -> Map InstKey Name -> Map Name AlloyFunction -> AlloyFunction -> AlloyFunction
applyRewrites rwMap instCache baseFnMap fn@AlloyFunction{afName, afBlocks, afParams = fnParams} =
    fn{afBlocks = map rewriteBlock afBlocks}
  where
    baseEnv = Map.fromList [(n, t) | (n, t) <- fnParams]

    rewriteBlock blk@ABlock{abInstrs, abParams} =
        let blockEnv = baseEnv `Map.union` Map.fromList [(n, t) | (n, t) <- abParams]
            (newInstrs, _, _) = foldl' (rewriteInstr blockEnv) ([], 0, blockEnv) abInstrs
        in blk{abInstrs = reverse newInstrs}

    rewriteInstr _env (acc, cid, currEnv) instr =
        case instr of
            ILet name ty op ->
                let (newOp, nextCid) = rewriteOp currEnv ty cid op
                    newEnv = Map.insert name ty currEnv
                in (ILet name ty newOp : acc, nextCid, newEnv)
            IEffect eff ->
                let newEff = rewriteEffect currEnv eff
                in (IEffect newEff : acc, cid, currEnv)

    rewriteOp _env ty cid op = case op of
        OpCall (Direct _) args ->
            case Map.lookup (afName, cid) rwMap of
                Just newName -> (OpCall (Direct newName) args, cid + 1)
                Nothing -> (op, cid + 1)
        OpDictCall _ _ _ args ->
            case Map.lookup (afName, cid) rwMap of
                Just newName -> (OpCall (Direct newName) args, cid + 1)
                Nothing -> (op, cid + 1)
        OpAllocClosure (OpVar lambdaName) envSize envTy ->
            -- Check if we need to rewrite the lambda name to a specialized version
            case Map.lookup lambdaName baseFnMap of
                Just lambdaFn ->
                    case matchClosureType (afParams lambdaFn) ty of
                        Just subst
                            | not (Map.null subst) && allConcreteSubst subst ->
                                let key = InstKey lambdaName (map (substType subst . snd) (afParams lambdaFn))
                                in case Map.lookup key instCache of
                                    Just specName -> (OpAllocClosure (OpVar specName) envSize envTy, cid)
                                    Nothing -> (op, cid)
                        _ -> (op, cid)
                Nothing -> (op, cid)
        _ -> (op, cid)

    matchClosureType :: [(Name, Type)] -> Type -> Maybe TySubst
    matchClosureType lambdaParams closureTy =
        let lambdaParamTypes = map snd (drop 1 lambdaParams)
        in matchFunctionParams lambdaParamTypes closureTy

    matchFunctionParams :: [Type] -> Type -> Maybe TySubst
    matchFunctionParams [] _ = Just Map.empty
    matchFunctionParams (p : ps) (TArrow argTy retTy) = do
        s1 <- unifyOne p argTy
        let ps' = map (substType s1) ps
        s2 <- matchFunctionParams ps' retTy
        Just (Map.union s2 s1)
    matchFunctionParams _ _ = Nothing

    rewriteEffect env eff = case eff of
        EffClosureSetEnv closure idx val ->
            EffClosureSetEnv closure idx (rewriteOperand env val)
        other -> other

    rewriteOperand env (OpVar varName)
        | Map.notMember varName env
        , Map.notMember varName baseFnMap =
            OpVar varName
    rewriteOperand _ op = op

specializeFunction :: String -> AlloyFunction -> TySubst -> AlloyFunction
specializeFunction _moduleName fn subst =
    let
        specializedTypes = map (substType subst . snd) (afParams fn)
        newName = makeMonomorphized (afName fn) specializedTypes
        newParams = [(n, substType subst t) | (n, t) <- afParams fn]
        newRet = substType subst (afReturnType fn)
        newBlocks = map (substBlock subst) (afBlocks fn)
    in
        fn
            { afName = newName
            , afParams = newParams
            , afReturnType = newRet
            , afBlocks = newBlocks
            }

substBlock :: TySubst -> ABlock -> ABlock
substBlock subst blk =
    blk
        { abParams = [(n, substType subst t) | (n, t) <- abParams blk]
        , abInstrs = map (substInstr subst) (abInstrs blk)
        }

substInstr :: TySubst -> AInstr -> AInstr
substInstr subst (ILet name ty op) =
    ILet name (substType subst ty) (substOp subst op)
substInstr subst (IEffect eff) = IEffect (substEffect subst eff)

substEffect :: TySubst -> AEffect -> AEffect
substEffect subst eff = case eff of
    EffClosureSetEnv closure idx val ->
        EffClosureSetEnv closure idx (substOperand subst val)
    other -> other

substOperand :: TySubst -> AOperand -> AOperand
substOperand subst (OpVar varName)
    | not (null subst)
    , Just _ <- nameBaseUnique varName =
        case Map.toList subst of
            [(_, concreteType)] ->
                OpVar (PN.makeInstanceMethod varName concreteType)
            _ -> OpVar varName
substOperand _ op = op

substOp :: TySubst -> AOp -> AOp
substOp subst op = case op of
    OpAllocStack ty -> OpAllocStack (substType subst ty)
    OpAllocHeap ty -> OpAllocHeap (substType subst ty)
    _ -> op

substType :: TySubst -> Type -> Type
substType subst ty = case ty of
    TVar v -> fromMaybe ty (Map.lookup v subst)
    TSkolem s ->
        let match v = tvId v == skName s
            found = listToMaybe [t | (v, t) <- Map.toList subst, match v]
        in fromMaybe ty found
    TApp t1 t2 -> TApp (substType subst t1) (substType subst t2)
    TArrow t1 t2 -> TArrow (substType subst t1) (substType subst t2)
    _ -> ty

matchCalleeParams :: [(Name, Type)] -> [Type] -> Maybe TySubst
matchCalleeParams params = unifyTypes (map snd params)

unifyTypes :: [Type] -> [Type] -> Maybe TySubst
unifyTypes [] [] = Just Map.empty
unifyTypes (p : ps) (a : as) = do
    s1 <- unifyOne p a
    let ps' = map (substType s1) ps
    let as' = map (substType s1) as
    s2 <- unifyTypes ps' as'
    Just (Map.union s2 s1)
unifyTypes _ _ = Nothing

unifyOne :: Type -> Type -> Maybe TySubst
unifyOne (TVar v) concrete = Just (Map.singleton v concrete)
unifyOne (TSkolem s) concrete =
    let syntheticVar = TypeVar{tvId = skName s, tvKind = skKind s}
    in Just (Map.singleton syntheticVar concrete)
unifyOne (TApp p1 p2) (TApp a1 a2) = do
    s1 <- unifyOne p1 a1
    let p2' = substType s1 p2
    let a2' = substType s1 a2
    s2 <- unifyOne p2' a2'
    Just (Map.union s2 s1)
unifyOne (TArrow p1 p2) (TArrow a1 a2) = do
    s1 <- unifyOne p1 a1
    let p2' = substType s1 p2
    let a2' = substType s1 a2
    s2 <- unifyOne p2' a2'
    Just (Map.union s2 s1)
unifyOne (TConstructor c1) (TConstructor c2)
    -- compare by id only, ignore kinds (they may differ due to partial application)
    | tcId c1 == tcId c2 = Just Map.empty
unifyOne _ _ = Nothing

eliminateAllTypeVars :: AlloyFunction -> AlloyFunction
eliminateAllTypeVars fn = fn

hasTypeVars :: AlloyFunction -> Bool
hasTypeVars AlloyFunction{afParams, afReturnType} =
    any (hasTypeVar . snd) afParams || hasTypeVar afReturnType
  where
    hasTypeVar (TVar _) = True
    hasTypeVar (TApp a b) = hasTypeVar a || hasTypeVar b
    hasTypeVar (TArrow a b) = hasTypeVar a || hasTypeVar b
    hasTypeVar _ = False

allConcreteSubst :: TySubst -> Bool
allConcreteSubst = all isConcrete . Map.elems
  where
    isConcrete (TVar _) = False
    isConcrete (TApp a b) = isConcrete a && isConcrete b
    isConcrete (TArrow a b) = isConcrete a && isConcrete b
    isConcrete _ = True

operandType :: Map Name AlloyFunction -> Map Name Type -> AOperand -> Maybe Type
operandType baseFnMap env (OpVar v) =
    case Map.lookup v env of
        Just t -> Just t
        Nothing -> fmap functionType (Map.lookup v baseFnMap)
operandType _ _ (OpConst c) = Just $ case c of
    CInt _ -> intType
    CString _ -> strType
    CBool _ -> boolType
    CUnit -> unitType

functionType :: AlloyFunction -> Type
functionType AlloyFunction{afParams, afReturnType} =
    foldr (TArrow . snd) afReturnType afParams

fnName :: AlloyFunction -> Name
fnName = afName

toFnMap :: [AlloyFunction] -> Map Name AlloyFunction
toFnMap = Map.fromList . map (\f -> (fnName f, f))

dedupByName :: [AlloyFunction] -> [AlloyFunction]
dedupByName fns = Map.elems (Map.fromList [(fnName f, f) | f <- fns])
