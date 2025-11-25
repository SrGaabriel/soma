{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Alloy.Monomorphize (
    monomorphizeModule,
    monomorphizeFunction,
    InstKey (..),
    TySubst,
) where

import Alloy.Ir
    ( ABlock (..)
    , ACallable (..)
    , AConst (..)
    , AInstr (..)
    , AOp (..)
    , AOperand (..)
    , AlloyFunction (..)
    , AlloyModule (..)
    )
import Alloy.Naming
    ( extractBaseTypeName
    , extractTypeName
    , makeInstanceMethodName
    , makeMonomorphicName
    )
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, listToMaybe)
import qualified Data.Set as Set
import Typing.Types
    ( TyVar (..)
    , Type (..)
    , boolType
    , intType
    , strType
    , TyConstructor (..)
    , SkolemVar (..)
    )
import Debug.Trace (trace)

type TySubst = Map TyVar Type

data InstKey = InstKey
    { ikBase :: String
    , ikArgs :: [Type]
    }
    deriving (Eq, Ord, Show)

type CallSiteId = Int
type RewriteMap = Map (String, CallSiteId) String

monomorphizeModule :: AlloyModule -> AlloyModule
monomorphizeModule m@AlloyModule{amName = moduleName, amFunctions = funcs} =
    let baseFnMap = toFnMap funcs
        !_ = trace "=== STARTING MONOMORPHIZATION ===" ()

        -- Phase 1: Fixpoint Scan
        (allFns, instCache) = monoFixpoint moduleName baseFnMap funcs Map.empty
        dedupedFns = dedupByName allFns

        -- Phase 2: Rewrite
        rwMap = computeRewriteMap baseFnMap instCache dedupedFns

        -- Apply rewrites
        rewrittenFns = map (applyRewrites rwMap) dedupedFns

        -- Phase 3: Cleanup
        specializedNames = Set.fromList (Map.elems instCache)
        isKept fn = afName fn `Set.member` specializedNames
                 || afName fn == "main"
                 || not (hasTypeVars fn)

        finalFns = map eliminateAllTypeVars $ filter isKept rewrittenFns

    in m { amFunctions = finalFns }

monomorphizeFunction :: String -> Map String AlloyFunction -> AlloyFunction -> (AlloyFunction, [AlloyFunction])
monomorphizeFunction moduleName baseFnMap fn =
    let (allFns, instCache) = monoFixpoint moduleName baseFnMap [fn] Map.empty
        rwMap = computeRewriteMap baseFnMap instCache allFns
        rewrittenAll = map (applyRewrites rwMap) allFns
        concreteAll = map eliminateAllTypeVars rewrittenAll
    in case concreteAll of
        [] -> (fn, [])
        (f : cs) -> (f, cs)


data CallResolution = CallResolution
    { crTargetFn :: AlloyFunction
    , crSubst    :: TySubst
    , crKey      :: InstKey
    }

resolveCallTarget :: Map String AlloyFunction -> Map String Type -> AOp -> Maybe CallResolution
resolveCallTarget baseFnMap env op =
    case op of
        OpCall (Direct calleeName) args -> resolveCommon calleeName args
        OpDictCall _ _ methodName args  -> resolveCommon methodName args
        _                               -> Nothing
  where
    resolveCommon name args =
        let resolvedName = resolveTraitMethod baseFnMap env name args
        in case Map.lookup resolvedName baseFnMap of
            Nothing -> Nothing
            Just calleeFn ->
                case mapM (operandType baseFnMap env) args of
                    Nothing -> Nothing
                    Just argTys ->
                        case matchCalleeParams (afParams calleeFn) argTys of
                            Just subst | not (Map.null subst) && allConcreteSubst subst ->
                                Just CallResolution
                                    { crTargetFn = calleeFn
                                    , crSubst = subst
                                    , crKey = InstKey (afName calleeFn) (map (substType subst . snd) (afParams calleeFn))
                                    }
                            _ -> Nothing


resolveTraitMethod :: Map String AlloyFunction -> Map String Type -> String -> [AOperand] -> String
resolveTraitMethod baseFnMap env methodName args
    | Nothing <- Map.lookup methodName baseFnMap =
        case mapM (operandType baseFnMap env) args of
            Just argTys ->
                let firstNonFunctionType = case argTys of
                        (TArrow _ _ : rest) -> listToMaybe rest
                        (ty : _) -> Just ty
                        [] -> Nothing
                in case firstNonFunctionType of
                    Just firstArgType ->
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
                    Nothing -> methodName
            _ -> methodName
    | otherwise = methodName


monoFixpoint :: String
             -> Map String AlloyFunction
             -> [AlloyFunction]
             -> Map InstKey String
             -> ([AlloyFunction], Map InstKey String)
monoFixpoint moduleName baseFnMap fns0 cache0 =
    let reqs = scanForRequests baseFnMap fns0
        newReqs = [ (b, s, k) | (b, s, k) <- reqs, Map.notMember k cache0 ]

        newClones =
            [ let baseFn = fromMaybe (error $ "Missing base fn: " ++ b) (Map.lookup b baseFnMap)
                  clone = specializeFunction moduleName baseFn s
              in (k, afName clone, clone)
            | (b, s, k) <- newReqs
            ]

        cache1 = foldl' (\acc (k, nm, _) -> Map.insert k nm acc) cache0 newClones
        fns1 = fns0 ++ [ c | (_, _, c) <- newClones ]
    in if null newClones
        then (fns0, cache0)
        else monoFixpoint moduleName baseFnMap fns1 cache1

scanForRequests :: Map String AlloyFunction -> [AlloyFunction] -> [(String, TySubst, InstKey)]
scanForRequests baseFnMap = concatMap (scanCallsInFunction baseFnMap)

scanCallsInFunction :: Map String AlloyFunction -> AlloyFunction -> [(String, TySubst, InstKey)]
scanCallsInFunction baseFnMap AlloyFunction{afParams, afBlocks} =
    let baseEnv = Map.fromList afParams
        (_, reqs) = foldl' scanBlock (baseEnv, []) afBlocks
    in reqs
  where
    scanBlock (env, reqs) ABlock{abParams, abInstrs} =
        let env' = env `Map.union` Map.fromList abParams
            step (currEnv, currReqs) instr =
                case instr of
                    ILet name ty op ->
                        let nextReqs = case resolveCallTarget baseFnMap currEnv op of
                                Just CallResolution{crTargetFn, crSubst, crKey} ->
                                    (afName crTargetFn, crSubst, crKey) : currReqs
                                Nothing -> currReqs
                        in (Map.insert name ty currEnv, nextReqs)
                    IEffect _ -> (currEnv, currReqs)
        in foldl' step (env', reqs) abInstrs

computeRewriteMap :: Map String AlloyFunction
                  -> Map InstKey String
                  -> [AlloyFunction]
                  -> RewriteMap
computeRewriteMap baseFnMap instCache fns =
    Map.fromList $ concatMap processFn fns
  where
    processFn AlloyFunction{afName, afParams, afBlocks} =
        let baseEnv = Map.fromList afParams
            -- outer fold: accumulates (CallSiteId, Rewrites) across blocks
            (_, rewrites) = foldl' (processBlock baseEnv) (0, []) afBlocks
        in map (\(cid, target) -> ((afName, cid), target)) rewrites

    processBlock baseEnv (startCid, startAcc) ABlock{abParams, abInstrs} =
        let
            blockEnv = baseEnv `Map.union` Map.fromList abParams
            
            -- we thread the environment strictly within the block, but pass Cid/Rewrites through
            initialState = (blockEnv, startCid, startAcc)
            
            step (env, cid, acc) instr =
                case instr of
                    ILet name ty op ->
                        let (nextCid, hit) = case resolveCallTarget baseFnMap env op of
                                Just CallResolution{crKey} ->
                                    case Map.lookup crKey instCache of
                                        Just specName -> (cid + 1, Just specName)
                                        Nothing       -> (cid + 1, Nothing)
                                Nothing -> 
                                    -- if resolution fails but it's a Call op, we MUST increment cid to keep indices aligned with the Scan phase
                                    (if isCallOp op then cid + 1 else cid, Nothing)

                            nextAcc = case hit of
                                Just target -> (cid, target) : acc
                                Nothing     -> acc
                            
                            nextEnv = Map.insert name ty env
                        in (nextEnv, nextCid, nextAcc)

                    IEffect _ -> (env, cid, acc)

            (_, finalCid, finalAcc) = foldl' step initialState abInstrs
        in (finalCid, finalAcc)

    isCallOp (OpCall _ _) = True
    isCallOp (OpDictCall {}) = True
    isCallOp _ = False

applyRewrites :: RewriteMap -> AlloyFunction -> AlloyFunction
applyRewrites rwMap fn@AlloyFunction{afName, afBlocks} =
    fn { afBlocks = map rewriteBlock afBlocks }
  where
    rewriteBlock blk@ABlock{abInstrs} =
        let (newInstrs, _) = foldl' rewriteInstr ([], 0) abInstrs
        in blk { abInstrs = reverse newInstrs }

    rewriteInstr (acc, cid) instr =
        case instr of
            ILet name ty op ->
                let (newOp, nextCid) = rewriteOp cid op
                in (ILet name ty newOp : acc, nextCid)
            other -> (other : acc, cid)

    rewriteOp cid op = case op of
        OpCall (Direct _) args ->
            case Map.lookup (afName, cid) rwMap of
                Just newName -> (OpCall (Direct newName) args, cid + 1)
                Nothing      -> (op, cid + 1)
        OpDictCall _ _ _ args ->
            case Map.lookup (afName, cid) rwMap of
                Just newName -> (OpCall (Direct newName) args, cid + 1)
                Nothing      -> (op, cid + 1)
        _ -> (op, cid)

specializeFunction :: String -> AlloyFunction -> TySubst -> AlloyFunction
specializeFunction _ fn subst =
    let newName   = makeMonomorphicName (afName fn) (map (substType subst . snd) (afParams fn))
        newParams = [ (n, substType subst t) | (n, t) <- afParams fn ]
        newRet    = substType subst (afReturnType fn)
        newBlocks = map (substBlock subst) (afBlocks fn)
    in fn { afName = newName
          , afParams = newParams
          , afReturnType = newRet
          , afBlocks = newBlocks
          }

substBlock :: TySubst -> ABlock -> ABlock
substBlock subst blk =
    blk { abParams = [ (n, substType subst t) | (n, t) <- abParams blk ]
        , abInstrs = map (substInstr subst) (abInstrs blk)
        }

substInstr :: TySubst -> AInstr -> AInstr
substInstr subst (ILet name ty op) =
    ILet name (substType subst ty) (substOp subst op)
substInstr _ (IEffect eff) = IEffect eff

substOp :: TySubst -> AOp -> AOp
substOp subst op = case op of
    OpAllocStack ty           -> OpAllocStack (substType subst ty)
    OpAllocHeap ty            -> OpAllocHeap (substType subst ty)
    _                         -> op

substType :: TySubst -> Type -> Type
substType subst ty = case ty of
    TVar v -> fromMaybe ty (Map.lookup v subst)
    TSkolem s ->
        let match v = tvId v == skName s
            found = listToMaybe [ t | (v, t) <- Map.toList subst, match v ]
        in fromMaybe ty found
    TApp t1 t2 -> TApp (substType subst t1) (substType subst t2)
    TArrow t1 t2 -> TArrow (substType subst t1) (substType subst t2)
    _ -> ty

matchCalleeParams :: [(String, Type)] -> [Type] -> Maybe TySubst
matchCalleeParams params args =
    unifyTypes (map snd params) args

unifyTypes :: [Type] -> [Type] -> Maybe TySubst
unifyTypes [] [] = Just Map.empty
unifyTypes (p:ps) (a:as) = do
    s1 <- unifyOne p a
    let ps' = map (substType s1) ps
    let as' = map (substType s1) as
    s2 <- unifyTypes ps' as'
    Just (Map.union s2 s1)
unifyTypes _ _ = Nothing

unifyOne :: Type -> Type -> Maybe TySubst
unifyOne (TVar v) concrete = Just (Map.singleton v concrete)
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
    | c1 == c2 = Just Map.empty
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

operandType :: Map String AlloyFunction -> Map String Type -> AOperand -> Maybe Type
operandType baseFnMap env (OpVar v) =
    case Map.lookup v env of
        Just t -> Just t
        Nothing -> fmap functionType (Map.lookup v baseFnMap)
operandType _ _ (OpConst c) = Just $ case c of
    CInt _ -> intType
    CString _ -> strType
    CBool _ -> boolType
    CUnit -> TConstructor (TypeConstructor "Unit" undefined)

functionType :: AlloyFunction -> Type
functionType AlloyFunction{afParams, afReturnType} =
    foldr (TArrow . snd) afReturnType afParams

toFnMap :: [AlloyFunction] -> Map String AlloyFunction
toFnMap = Map.fromList . map (\f -> (afName f, f))

dedupByName :: [AlloyFunction] -> [AlloyFunction]
dedupByName fns = Map.elems (Map.fromList [(afName f, f) | f <- fns])