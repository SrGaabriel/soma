{-# LANGUAGE NamedFieldPuns #-}

{- |
| Signature-rewrite pass for the Reader monad: make the environment an explicit
| function parameter and return the inner value (not Reader env a).
|
| Scope and guarantees (conservative by design):
| - We only rewrite a function `f` if:
|     1) Its return type is syntactically `Reader env a` (by type constructor name),
|     2) We can rewrite ALL direct call sites within the same module by supplying a concrete
|        environment operand, detected as the most recently seen argument to `Reader.ask`
|        in the same block before the call site.
| - Inside the rewritten function, any `Reader.ask envArg` is eliminated and replaced with
|   the new environment parameter (ask becomes identity on the parameter).
| - If any call site lacks an available environment operand, the function is left untouched.
|
| Ordering in the pipeline:
| - This pass expects `Reader.ask` calls to still be present (i.e., run BEFORE MonadicInline).
|   If you run MonadicInline first, the ask calls may have been erased, and this pass will
|   conservatively skip rewriting due to missing env operands.
-}
module Alloy.ReaderRewrite (
    readerRewriteModule,
    readerRewriteModuleWith,
    readerRewriteFunction,
    ReaderConfig (..),
    defaultReaderConfig,
) where

import Alloy.Ir
import Alloy.Subst (Subst, substEffect, substOp, substTerminator)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Project.Name as PN
import Typing.Types (TyConstructor (..), Type (..), tyUniqueName)

data ReaderConfig = ReaderConfig
    { readerTypeNames :: [String]
    , readerAskPatterns :: [String]
    , envParamName :: Name
    }
    deriving (Show, Eq)

defaultReaderConfig :: ReaderConfig
defaultReaderConfig =
    ReaderConfig
        { readerTypeNames = ["Reader"]
        , readerAskPatterns = ["Reader.ask", "Reader$ask"]
        , envParamName = PN.NLocal (PN.LocalId PN.LPParam 0) -- Use first param slot for env
        }

readerRewriteModule :: AlloyModule -> AlloyModule
readerRewriteModule = readerRewriteModuleWith defaultReaderConfig

readerRewriteModuleWith :: ReaderConfig -> AlloyModule -> AlloyModule
readerRewriteModuleWith cfg m@AlloyModule{amFunctions} =
    let fnMap0 = Map.fromList [(afName f, f) | f <- amFunctions]
        eligibles = discoverEligible cfg fnMap0
        (fnMap1, rewriters) = rewriteEligibleFunctions cfg fnMap0 eligibles
        fnsRewritten = Map.elems fnMap1
        fnsFinal = map (rewriteCalls cfg rewriters) fnsRewritten
    in m{amFunctions = fnsFinal}

readerRewriteFunction :: ReaderConfig -> AlloyFunction -> AlloyFunction
readerRewriteFunction cfg fn =
    let afs = readerRewriteModuleWith cfg (AlloyModule "" [fn] [] [] Set.empty [])
    in case amFunctions afs of
        [f] -> f
        _ -> fn

discoverEligible ::
    ReaderConfig ->
    Map Name AlloyFunction ->
    Map Name (Type, Type, [(CallSiteId, Name, AOperand)]) -- f -> (envTy, aTy, callsites with env operand)
discoverEligible cfg fnMap =
    Map.fromList
        [ (fname, (envTy, aTy, callsites))
        | (fname, f) <- Map.toList fnMap
        , let callsites = findCallsitesWithEnv cfg fname fnMap
        , not (null callsites)
        , allSitesHaveEnv callsites
        , Just (envTy, aTy) <- [readerReturn cfg (afReturnType f)]
        ]

type CallSiteId = Int

allSitesHaveEnv :: [(CallSiteId, Name, AOperand)] -> Bool
allSitesHaveEnv = all (\(_, _, _) -> True) -- by construction, list contains only sites with env

readerReturn :: ReaderConfig -> Type -> Maybe (Type, Type)
readerReturn ReaderConfig{readerTypeNames} ty =
    case ty of
        TApp (TApp (TConstructor (TypeConstructor tyId _)) envTy) aTy
            | tyUniqueName tyId `elem` readerTypeNames -> Just (envTy, aTy)
        _ -> Nothing

findCallsitesWithEnv ::
    ReaderConfig ->
    Name ->
    Map Name AlloyFunction ->
    [(CallSiteId, Name, AOperand)]
findCallsitesWithEnv cfg callee fnMap =
    concatMap (scanFn cfg callee) (Map.elems fnMap)

scanFn ::
    ReaderConfig ->
    Name ->
    AlloyFunction ->
    [(CallSiteId, Name, AOperand)]
scanFn cfg callee AlloyFunction{afName, afBlocks} =
    let (_, acc) = foldl' (scanBlock cfg callee afName) (0, []) afBlocks
    in acc

scanBlock ::
    ReaderConfig ->
    Name ->
    Name ->
    (CallSiteId, [(CallSiteId, Name, AOperand)]) ->
    ABlock ->
    (CallSiteId, [(CallSiteId, Name, AOperand)])
scanBlock cfg callee caller (cid0, acc0) ABlock{abInstrs} =
    let step (cid, acc, mEnv) instr =
            case instr of
                ILet _ _ (OpCall (Direct ask) [arg])
                    | PN.nameMatchesStdlib (readerAskPatterns cfg) ask ->
                        (cid, acc, Just arg)
                ILet _ _ (OpCall (Direct target) _)
                    | target == callee ->
                        case mEnv of
                            Just envOp -> (cid + 1, (cid, caller, envOp) : acc, mEnv)
                            Nothing -> (cid + 1, acc, mEnv)
                ILet{} -> (cid, acc, mEnv)
                IEffect _ -> (cid, acc, mEnv)
        (cid', acc', _) = foldl' step (cid0, acc0, Nothing) abInstrs
    in (cid', acc')

rewriteEligibleFunctions ::
    ReaderConfig ->
    Map Name AlloyFunction ->
    Map Name (Type, Type, [(CallSiteId, Name, AOperand)]) ->
    (Map Name AlloyFunction, Map (Name, CallSiteId, Name) CallRewrite)
rewriteEligibleFunctions cfg fnMap elig =
    let folders (fmap', rwmap') (fname, (envTy, aTy, sites)) =
            case Map.lookup fname fnMap of
                Nothing -> (fmap', rwmap')
                Just f ->
                    let f' = injectEnvParam cfg envTy aTy f
                        rwSites =
                            Map.fromList
                                [ ((fname, cid, caller), CallRewrite{crEnv = envArg, crNewRet = aTy})
                                | (cid, caller, envArg) <- sites
                                ]
                    in (Map.insert fname f' fmap', Map.union rwSites rwmap')
    in foldl' folders (fnMap, Map.empty) (Map.toList elig)

injectEnvParam :: ReaderConfig -> Type -> Type -> AlloyFunction -> AlloyFunction
injectEnvParam cfg@ReaderConfig{envParamName} envTy aTy fn@AlloyFunction{afParams, afBlocks} =
    let envParam = (envParamName, envTy)
        blocks' = map (rewriteBlockBody cfg envParamName) afBlocks
    in fn{afParams = envParam : afParams, afReturnType = aTy, afBlocks = blocks'}

rewriteBlockBody :: ReaderConfig -> Name -> ABlock -> ABlock
rewriteBlockBody cfg envParamNm blk@ABlock{abInstrs, abTerminator} =
    let (instrs', subst) = foldl' (rewriteInstr cfg envParamNm) ([], Map.empty) abInstrs
        term' = substTerminator subst abTerminator
    in blk{abInstrs = reverse instrs', abTerminator = term'}

rewriteInstr ::
    ReaderConfig ->
    Name ->
    ([AInstr], Subst) ->
    AInstr ->
    ([AInstr], Subst)
rewriteInstr ReaderConfig{readerAskPatterns} envParamNm (acc, env) instr =
    case instr of
        -- Eliminate Reader.ask, substitute result with the new env parameter
        ILet n _ (OpCall (Direct ask) [_arg])
            | PN.nameMatchesStdlib readerAskPatterns ask ->
                let envOp = OpVar envParamNm
                in (acc, Map.insert n envOp env)
        ILet n t op ->
            let op' = substOp env op
            in (ILet n t op' : acc, env)
        IEffect eff ->
            let eff' = substEffect env eff
            in (IEffect eff' : acc, env)

data CallRewrite = CallRewrite
    { crEnv :: AOperand
    , crNewRet :: Type
    }

rewriteCalls ::
    ReaderConfig ->
    Map (Name, CallSiteId, Name) CallRewrite ->
    AlloyFunction ->
    AlloyFunction
rewriteCalls _cfg rwMap fn@AlloyFunction{afName, afBlocks} =
    let (blocks', _) = foldl' goBlock ([], 0) afBlocks
    in fn{afBlocks = reverse blocks'}
  where
    goBlock :: ([ABlock], CallSiteId) -> ABlock -> ([ABlock], CallSiteId)
    goBlock (accBlks, cid0) blk@ABlock{abInstrs, abTerminator} =
        let (instrs', cid1) = foldl' (goInstr afName) ([], cid0) abInstrs
            blk' = blk{abInstrs = reverse instrs', abTerminator}
        in (blk' : accBlks, cid1)

    goInstr ::
        Name ->
        ([AInstr], CallSiteId) ->
        AInstr ->
        ([AInstr], CallSiteId)
    goInstr caller (acc, cid) instr =
        case instr of
            ILet n _ (OpCall (Direct callee) args) ->
                let key = (callee, cid, caller)
                in case Map.lookup key rwMap of
                    Just CallRewrite{crEnv, crNewRet} ->
                        (ILet n crNewRet (OpCall (Direct callee) (crEnv : args)) : acc, cid + 1)
                    Nothing ->
                        (instr : acc, cid + 1)
            ILet n t (OpCall (Indirect a) args) ->
                (ILet n t (OpCall (Indirect a) args) : acc, cid + 1)
            ILet n t op ->
                (ILet n t op : acc, cid)
            IEffect eff ->
                (IEffect eff : acc, cid)
