{-# LANGUAGE NamedFieldPuns #-}

module Alloy.CSE (
    cseModule,
    cseFunction,
    cseModuleGlobal,
    cseFunctionGlobal,
) where

import Alloy.Ir
import Alloy.Uniqueness (FunctionReport (..), LocalUniq (..), Uniqueness (..), analyzeFunction)
import Data.List (foldl')
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

-- Public: run the CSE pass across the whole module
-- This is a simple local pass that:
-- - removes redundant EffStore p v when the last known store for unique pointer p is also v
-- - removes redundant loads ILet x = OpLoad p when the last known store for unique pointer p is v,
--   by substituting all uses of x with v and dropping the load
-- The optimizations are only applied when 'p' is a unique, non-escaping ref as determined by
-- Alloy.Uniqueness.analyzeFunction. We keep analysis conservative and per-block local
cseModule :: AlloyModule -> AlloyModule
cseModule m@AlloyModule{amFunctions} =
    m{amFunctions = map (cseFunction . id) amFunctions}

cseFunction :: AlloyFunction -> AlloyFunction
cseFunction fn =
    let FunctionReport{frLocalUniq = LocalUniq{luLocals}} = analyzeFunction fn
        uniqueLocals = Set.fromList [n | (n, Unique) <- Map.toList luLocals]
    in cseFunctionWithUniqueSet uniqueLocals fn

cseFunctionWithUniqueSet :: Set Name -> AlloyFunction -> AlloyFunction
cseFunctionWithUniqueSet uniqueRefs fn@AlloyFunction{afBlocks} =
    let (blocks', _) = foldl' step ([], Map.empty) afBlocks
    in fn{afBlocks = reverse blocks'}
  where
    -- todo: extend later to simple forwarder inlining

    step :: ([ABlock], Subst) -> ABlock -> ([ABlock], Subst)

    step (acc, _) blk =
        let blk' = cseBlock uniqueRefs blk
        in (blk' : acc, Map.empty)

buildPredCount :: [ABlock] -> Map BlockName Int
buildPredCount blks =
    let addPred m b = Map.insertWith (+) b 1 m
        succs t =
            case t of
                ABr b _ -> [b]
                ACondBr _ tb _ fb _ -> [tb, fb]
                ASwitch _ cs mdef -> maybe (map snd cs) (: map snd cs) mdef
                ARet _ -> []
                AUnreachable -> []
        tally m ABlock{abTerminator} = foldl' addPred m (succs abTerminator)
    in foldl' tally Map.empty blks

cseFunctionGlobalWithUniqueSet :: Set Name -> AlloyFunction -> AlloyFunction
cseFunctionGlobalWithUniqueSet uniqueRefs fn@AlloyFunction{afBlocks} =
    let preds = buildPredCount afBlocks
        process :: Map Name AOperand -> [ABlock] -> [ABlock]
        process _ [] = []
        process inStores (blk : rest) =
            let (blk', outStores) = cseBlockWithInit uniqueRefs inStores blk
                nextStores =
                    case rest of
                        (nxt : _) ->
                            case abTerminator blk of
                                ABr b _ | b == abName nxt && Map.findWithDefault 0 (abName nxt) preds == 1 -> outStores
                                _ -> Map.empty
                        [] -> Map.empty
            in blk' : process nextStores rest
        blocks' = process Map.empty afBlocks
    in fn{afBlocks = blocks'}

cseFunctionGlobal :: AlloyFunction -> AlloyFunction
cseFunctionGlobal fn =
    let FunctionReport{frLocalUniq = LocalUniq{luLocals}} = analyzeFunction fn
        uniqueLocals = Set.fromList [n | (n, Unique) <- Map.toList luLocals]
    in cseFunctionGlobalWithUniqueSet uniqueLocals fn

cseModuleGlobal :: AlloyModule -> AlloyModule
cseModuleGlobal m@AlloyModule{amFunctions} =
    m{amFunctions = map cseFunctionGlobal amFunctions}

cseBlock :: Set Name -> ABlock -> ABlock
cseBlock uniqueRefs blk =
    fst (cseBlockWithInit uniqueRefs Map.empty blk)

cseBlockWithInit :: Set Name -> Map Name AOperand -> ABlock -> (ABlock, Map Name AOperand)
cseBlockWithInit uniqueRefs initStores blk@ABlock{abInstrs, abTerminator} =
    let initState =
            BlockState
                { bsSubst = Map.empty
                , bsStoreVal = initStores
                }
        (instrs', state') = foldl' (cseInstr uniqueRefs) ([], initState) abInstrs

        term' = substTerminator (bsSubst state') abTerminator

        blk' = blk{abInstrs = reverse instrs', abTerminator = term'}
    in (blk', bsStoreVal state')

data BlockState = BlockState
    { bsSubst :: Subst
    , bsStoreVal :: Map Name AOperand
    }

type Subst = Map Name AOperand

cseInstr :: Set Name -> ([AInstr], BlockState) -> AInstr -> ([AInstr], BlockState)
cseInstr uniqueRefs (acc, st@BlockState{bsSubst, bsStoreVal}) instr =
    case instr of
        ILet n ty op ->
            let op' = substOp bsSubst op
            in case op' of
                OpLoad (OpVar p)
                    | Set.member p uniqueRefs
                    , Just v <- Map.lookup p bsStoreVal ->
                        let subst' = Map.insert n v bsSubst
                        in (acc, st{bsSubst = subst', bsStoreVal = bsStoreVal})
                _ ->
                    (ILet n ty op' : acc, st)
        IEffect eff ->
            let eff' = substEffect bsSubst eff
            in case eff' of
                EffStore (OpVar p) v
                    | Set.member p uniqueRefs ->
                        let v' = v
                            same = Map.lookup p bsStoreVal == Just v'
                            storeVal' = Map.insert p v' bsStoreVal
                        in if same
                            then
                                (acc, st{bsStoreVal = storeVal'})
                            else
                                (IEffect (EffStore (OpVar p) v') : acc, st{bsStoreVal = storeVal'})
                EffStoreIndex (OpVar p) _ _
                    | Set.member p uniqueRefs ->
                        (IEffect eff' : acc, st{bsStoreVal = Map.delete p bsStoreVal})
                EffDrop _ ->
                    (IEffect eff' : acc, st)
                _ ->
                    (IEffect eff' : acc, st)

substOperand :: Subst -> AOperand -> AOperand
substOperand env (OpVar n) = Map.findWithDefault (OpVar n) n env
substOperand _ a@(OpConst _) = a

substCallable :: Subst -> ACallable -> ACallable
substCallable _ (Direct n) = Direct n
substCallable env (Indirect a) = Indirect (substOperand env a)

substOp :: Subst -> AOp -> AOp
substOp env op =
    case op of
        OpBin k a b -> OpBin k (substOperand env a) (substOperand env b)
        OpUnary k a -> OpUnary k (substOperand env a)
        OpCmp k a b -> OpCmp k (substOperand env a) (substOperand env b)
        OpLoad a -> OpLoad (substOperand env a)
        OpAllocStack t -> OpAllocStack t
        OpAllocHeap t -> OpAllocHeap t
        OpCall callee args -> OpCall (substCallable env callee) (map (substOperand env) args)
        OpConstruct tn tag fields -> OpConstruct tn tag (map (substOperand env) fields)
        OpTagOf a -> OpTagOf (substOperand env a)
        OpProject a i -> OpProject (substOperand env a) i
        OpIndex a i -> OpIndex (substOperand env a) (substOperand env i)
        OpMakeArray xs -> OpMakeArray (map (substOperand env) xs)
        OpMakeTuple xs -> OpMakeTuple (map (substOperand env) xs)

substEffect :: Subst -> AEffect -> AEffect
substEffect env eff =
    case eff of
        EffStore p v -> EffStore (substOperand env p) (substOperand env v)
        EffStoreIndex a i v -> EffStoreIndex (substOperand env a) (substOperand env i) (substOperand env v)
        EffDrop a -> EffDrop (substOperand env a)

substTerminator :: Subst -> ATerminator -> ATerminator
substTerminator env t =
    case t of
        ABr b args -> ABr b (map (substOperand env) args)
        ACondBr c tb ta fb fa ->
            ACondBr
                (substOperand env c)
                tb
                (map (substOperand env) ta)
                fb
                (map (substOperand env) fa)
        ASwitch v cases mdef ->
            ASwitch (substOperand env v) cases mdef
        ARet mv -> ARet (fmap (substOperand env) mv)
        AUnreachable -> AUnreachable
