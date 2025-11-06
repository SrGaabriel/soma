{-# LANGUAGE NamedFieldPuns #-}

module Alloy.Uniqueness (
    analyzeModule,
    analyzeFunction,
    annotateForInPlace,
    defaultPolicy,
    ModuleReport (..),
    FunctionReport (..),
    LocalUniq (..),
    Uniqueness (..),
    Decision (..),
    Policy (..),
) where

import Alloy.Ir
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

data Uniqueness
    = Unique
    | Shared
    deriving (Eq, Ord, Show)

data LocalUniq = LocalUniq
    { luParams :: Map Name Uniqueness
    , luLocals :: Map Name Uniqueness
    , luBlockParams :: Map BlockName (Map Name Uniqueness)
    }
    deriving (Eq, Show)

newtype Decision -- todo make this an ADT
    = MutateInPlace Name
    deriving (Eq, Ord, Show)

data FunctionReport = FunctionReport
    { frFunctionName :: Name
    , frLocalUniq :: LocalUniq
    , frDecisions :: [Decision]
    }
    deriving (Eq, Show)

newtype ModuleReport = ModuleReport
    { mrFunctions :: Map Name FunctionReport
    }
    deriving (Eq, Show)

newtype Policy = Policy
    { allowAllocStackInPlace :: Bool
    }
    deriving (Eq, Show)

defaultPolicy :: Policy
defaultPolicy = Policy{allowAllocStackInPlace = True}

analyzeModule :: AlloyModule -> ModuleReport
analyzeModule AlloyModule{amFunctions} =
    let funReports = map analyzeFunction amFunctions
    in ModuleReport{mrFunctions = Map.fromList [(frFunctionName r, r) | r <- funReports]}

analyzeFunction :: AlloyFunction -> FunctionReport
analyzeFunction AlloyFunction{afName, afParams, afBlocks} =
    let paramUniq = Map.fromList [(p, Shared) | (p, _) <- afParams]
        (allocs, useMap) = collectAllocationsAndUses afBlocks
        localUniq = decideLocals allocs useMap
        blockParamUniq =
            Map.fromList
                [ (abName b, Map.fromList [(n, Shared) | (n, _) <- abParams b])
                | b <- afBlocks
                ]
        decisions = decideInPlace defaultPolicy localUniq
    in FunctionReport
        { frFunctionName = afName
        , frLocalUniq =
            LocalUniq
                { luParams = paramUniq
                , luLocals = localUniq
                , luBlockParams = blockParamUniq
                }
        , frDecisions = decisions
        }

annotateForInPlace :: Policy -> AlloyFunction -> FunctionReport -> AlloyFunction
annotateForInPlace _policy fn _report = fn

collectAllocationsAndUses :: [ABlock] -> (Set.Set Name, Map Name [UseKind])
collectAllocationsAndUses blocks =
    let step (allocsAcc, usesAcc) b =
            let (allocsB, usesB) = collectInBlock b
            in ( Set.union allocsAcc allocsB
               , mergeUseMaps usesAcc usesB
               )
    in foldl' step (Set.empty, Map.empty) blocks

collectInBlock :: ABlock -> (Set.Set Name, Map Name [UseKind])
collectInBlock ABlock{abInstrs, abTerminator, abName} =
    let (allocsI, usesI) = collectInInstrs abName abInstrs
        usesT = collectInTerminator abName abTerminator
    in (allocsI, mergeUseMaps usesI usesT)

collectInInstrs :: BlockName -> [AInstr] -> (Set.Set Name, Map Name [UseKind])
collectInInstrs blk instrs =
    let folder (allocsAcc, usesAcc, idx) instr =
            case instr of
                ILet n _ (OpAllocStack _) ->
                    ( Set.insert n allocsAcc
                    , usesAcc
                    , idx + 1
                    )
                ILet _ _ op ->
                    let usesHere = usesFromOp blk idx op
                    in (allocsAcc, mergeUseMaps usesAcc usesHere, idx + 1)
                IEffect eff ->
                    let usesHere = usesFromEffect blk idx eff
                    in (allocsAcc, mergeUseMaps usesAcc usesHere, idx + 1)
        (allocs, uses, _) = foldl' folder (Set.empty, Map.empty, 0 :: Int) instrs
    in (allocs, uses)

collectInTerminator :: BlockName -> ATerminator -> Map Name [UseKind]
collectInTerminator blk t =
    case t of
        ABr _ args ->
            mergeAll [singleUse v (UseBrArg blk) | v@(OpVar _) <- args]
        ACondBr c _ ta _ fa ->
            mergeAll (singleUseIfVar c (UseCond blk) : [singleUseIfVar a (UseBrArg blk) | a <- ta ++ fa])
        ASwitch v _ _ ->
            mergeAll [singleUseIfVar v (UseSwitchVal blk)]
        ARet mv ->
            case mv of
                Just (OpVar n) -> Map.singleton n [UseReturn blk]
                _ -> Map.empty
        AUnreachable -> Map.empty

usesFromOp :: BlockName -> Int -> AOp -> Map Name [UseKind]
usesFromOp blk idx op =
    case op of
        OpBin _ a b ->
            mergeAll [singleUseIfVar a (UseBinArg blk idx), singleUseIfVar b (UseBinArg blk idx)]
        OpUnary _ a -> singleUseIfVar a (UseUnaryArg blk idx)
        OpCmp _ a b ->
            mergeAll [singleUseIfVar a (UseCmpArg blk idx), singleUseIfVar b (UseCmpArg blk idx)]
        OpLoad a -> singleUseIfVar a (UseLoadPtr blk idx)
        OpAllocStack _ -> Map.empty
        OpAllocHeap _ -> Map.empty
        OpCall callee args ->
            let calleeUse =
                    case callee of
                        Direct _ -> Map.empty
                        Indirect (OpVar n) -> Map.singleton n [UseCallIndirect blk idx]
                        Indirect _ -> Map.empty
                argUses = [singleUseIfVar a (UseCallArg blk idx j) | (j, a) <- zip [0 ..] args]
            in mergeUseMaps calleeUse (mergeAll argUses)
        OpConstruct _ _ fields ->
            mergeAll [singleUseIfVar a (UseAggValue blk idx) | a <- fields]
        OpTagOf a -> singleUseIfVar a (UseAggRead blk idx)
        OpProject a _ -> singleUseIfVar a (UseAggRead blk idx)
        OpIndex base ix ->
            mergeAll [singleUseIfVar base (UseIndexBase blk idx), singleUseIfVar ix (UseIndexIdx blk idx)]
        OpMakeArray xs ->
            mergeAll [singleUseIfVar a (UseAggValue blk idx) | a <- xs]
        OpMakeTuple xs ->
            mergeAll [singleUseIfVar a (UseAggValue blk idx) | a <- xs]

usesFromEffect :: BlockName -> Int -> AEffect -> Map Name [UseKind]
usesFromEffect blk idx eff =
    case eff of
        EffStore p v ->
            mergeAll [singleUseIfVar p (UseStorePtr blk idx), singleUseIfVar v (UseStoreVal blk idx)]
        EffStoreIndex a i v ->
            mergeAll
                [ singleUseIfVar a (UseStorePtr blk idx)
                , singleUseIfVar i (UseIndexIdx blk idx)
                , singleUseIfVar v (UseStoreVal blk idx)
                ]
        EffDrop a -> singleUseIfVar a (UseDrop blk idx)

data UseKind
    = UseCallArg BlockName Int Int
    | UseCallIndirect BlockName Int
    | UseReturn BlockName
    | UseStoreVal BlockName Int
    | UseAggValue BlockName Int
    | UseStorePtr BlockName Int
    | UseLoadPtr BlockName Int
    | UseAggRead BlockName Int
    | UseIndexBase BlockName Int
    | UseIndexIdx BlockName Int
    | UseBinArg BlockName Int
    | UseUnaryArg BlockName Int
    | UseCmpArg BlockName Int
    | UseBrArg BlockName
    | UseCond BlockName
    | UseSwitchVal BlockName
    | UseDrop BlockName Int
    deriving (Eq, Ord, Show)

singleUseIfVar :: AOperand -> UseKind -> Map Name [UseKind]
singleUseIfVar (OpVar n) k = Map.singleton n [k]
singleUseIfVar _ _ = Map.empty

singleUse :: AOperand -> UseKind -> Map Name [UseKind]
singleUse (OpVar n) k = Map.singleton n [k]
singleUse _ _ = Map.empty

mergeUseMaps :: Map Name [UseKind] -> Map Name [UseKind] -> Map Name [UseKind]
mergeUseMaps = Map.unionWith (++)

mergeAll :: [Map Name [UseKind]] -> Map Name [UseKind]
mergeAll = foldl' mergeUseMaps Map.empty

decideLocals :: Set.Set Name -> Map Name [UseKind] -> Map Name Uniqueness
decideLocals allocs uses =
    Map.fromList
        [ (n, if isNonEscaping n (Map.findWithDefault [] n uses) then Unique else Shared)
        | n <- Set.toList allocs
        ]
        `Map.union` Map.fromList
            [ (n, Shared)
            | n <- Map.keys uses
            , Set.notMember n allocs
            ]

isNonEscaping :: Name -> [UseKind] -> Bool
isNonEscaping _ [] = True
isNonEscaping _ ks = not (any isEscapeUse ks)

isEscapeUse :: UseKind -> Bool
isEscapeUse k =
    case k of
        UseCallArg{} -> True
        UseCallIndirect{} -> True
        UseReturn{} -> True
        UseStoreVal{} -> True
        UseAggValue{} -> True
        _ -> False

decideInPlace :: Policy -> Map Name Uniqueness -> [Decision]
decideInPlace Policy{allowAllocStackInPlace} locals
    | not allowAllocStackInPlace = []
    | otherwise =
        [ MutateInPlace n
        | (n, Unique) <- Map.toList locals
        ]
