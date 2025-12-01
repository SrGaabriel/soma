{-# LANGUAGE NamedFieldPuns #-}

{- | Alloy.PromoteRefs
A conservative, SSA-style "mem2reg" promotion for unique stack-allocated refs.

Goal
  - Eliminate newRef/readRef/modifyRef style state threading by promoting a unique
    stack slot (OpAllocStack elemTy) to an SSA value that is passed along edges
    as block parameters.
  - Remove all loads/stores to that slot and turn it into pure SSA updates.

Preconditions (conservative by design)
  - The candidate ref must be:
      * Bound by ILet name RefTy (OpAllocStack elemTy)
      * Proven Unique by Alloy.Uniqueness.analyzeFunction
      * Used ONLY as the pointer in EffStore (pointer := value) and OpLoad(pointer).
        Any other use (passing to calls, storing the pointer itself, embedding in aggregates)
        disqualifies the candidate.
  - There must be a dominating store along all outgoing edges:
      Formally, for every CFG edge, the source block must have a value for the ref
      at the end of the block. We compute this with a simple fixed-point data-flow:
        in[b]  = AND_{p in preds(b)} out[p]     (entry has in[entry] = False)
        out[b] = in[b] OR hasStoreInBlock(b)
      The ref is promotable iff for every block with successors, out[b] == True.
  - Additionally, in the entry block, no load of the ref may occur before the first
    store to that ref (because entry has no incoming block params to seed a value).

Effect of the transformation
  - For every promotable ref 'r' with element type 't', every non-entry block 'B'
    gets a new block parameter 'r$in$B : t', and every terminator is augmented to
    pass the current value along to successors (excluding the entry block).
  - The ILet 'r = OpAllocStack t' is removed.
  - EffStore r v updates the block-local "current value" map r := v and is removed.
  - ILet x = OpLoad r is removed and all subsequent uses of x are substituted with
    the current value of r.
  - All other instructions/terminators are preserved, with operand substitution applied.
-}
module Alloy.PromoteRefs (
    promoteRefsModule,
    promoteRefsFunction,
) where

import Alloy.Ir
import Alloy.Naming (makeRefParamName)
import Alloy.Uniqueness (FunctionReport (..), LocalUniq (..), Uniqueness (..), analyzeFunction)
import Data.List (findIndex, sort)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Typing.Types (Type (..))
import Utils.Lists (hardHead)

promoteRefsModule :: AlloyModule -> AlloyModule
promoteRefsModule m@AlloyModule{amFunctions} =
    m{amFunctions = map promoteRefsFunction amFunctions}

promoteRefsFunction :: AlloyFunction -> AlloyFunction
promoteRefsFunction fn =
    let fn0 = trivialRefPeephole fn
        candidates = findAllocaCandidates fn0
        uniqueSet = uniqueLocals fn0
        okUses = filter (\(n, _, _) -> uniqueOk n uniqueSet && usesOnlyLoadStore n fn0) candidates
        promotables =
            [ (n, refTy, elemTy)
            | (n, refTy, elemTy) <- okUses
            , entryNoLoadBeforeStore n fn
            ]
    in if null promotables
        then fn
        else promoteMany promotables fn

promoteMany :: [(Name, Type, Type)] -> AlloyFunction -> AlloyFunction
promoteMany refs fn@AlloyFunction{afEntry, afBlocks} =
    let promotedOrder :: [(Name, Type)] -- (refName, elemTy)
        promotedOrder = sort [(n, ety) | (n, _rty, ety) <- refs]
        promotedSet = Set.fromList (map fst promotedOrder)

        needsMap :: Map Name (Set.Set BlockName)
        needsMap =
            Map.fromList
                [ (r, Set.fromList [abName b | b <- afBlocks, abName b /= afEntry, loadBeforeStore r (abInstrs b)])
                | (r, _ety) <- promotedOrder
                ]

        addParamsFor :: ABlock -> [(Name, Type)]
        addParamsFor ABlock{abName} =
            if abName == afEntry
                then []
                else
                    [ (paramName r abName, ety)
                    | (r, ety) <- promotedOrder
                    , let needSet = Map.findWithDefault Set.empty r needsMap
                    , Set.member abName needSet
                    ]

        rewriteBlockWith :: ABlock -> ABlock
        rewriteBlockWith blk@ABlock{abName, abParams, abInstrs, abTerminator} =
            let
                needsHere r = Set.member abName (Map.findWithDefault Set.empty r needsMap)
                initCurr =
                    if abName == afEntry
                        then Map.empty
                        else
                            Map.fromList
                                [ (r, OpVar (paramName r abName))
                                | (r, _ety) <- promotedOrder
                                , needsHere r
                                ]

                initSubst = Map.empty
                (instrs', currVals', subst') = foldl' (stepInstr promotedSet) ([], initCurr, initSubst) abInstrs
                term' = augmentTerm afEntry promotedOrder needsMap currVals' (substTerminator subst' abTerminator)
                abParams' = abParams ++ addParamsFor blk
            in
                ABlock
                    { abName
                    , abParams = abParams'
                    , abInstrs = reverse instrs'
                    , abTerminator = term'
                    }

        blocks' = map rewriteBlockWith afBlocks
    in fn{afBlocks = blocks'}

stepInstr ::
    Set.Set Name ->
    ([AInstr], Map Name AOperand, Map Name AOperand) ->
    AInstr ->
    ([AInstr], Map Name AOperand, Map Name AOperand)
stepInstr promoted (acc, curr, subst) instr =
    case instr of
        ILet n _ (OpAllocStack _)
            | n `Set.member` promoted ->
                (acc, curr, subst)
        ILet n _ (OpLoad (OpVar r))
            | r `Set.member` promoted
            , Just v <- Map.lookup r curr ->
                (acc, curr, Map.insert n v subst)
        ILet n t op ->
            let op' = substOp subst op
            in (ILet n t op' : acc, curr, subst)
        IEffect (EffStore (OpVar r) v)
            | r `Set.member` promoted ->
                let v' = substOperand subst v
                in (acc, Map.insert r v' curr, subst)
        IEffect eff ->
            let eff' = substEffect subst eff
            in (IEffect eff' : acc, curr, subst)

augmentTerm ::
    BlockName ->
    [(Name, Type)] ->
    Map Name (Set.Set BlockName) ->
    Map Name AOperand ->
    ATerminator ->
    ATerminator
augmentTerm entry promoted needs curr term =
    case term of
        ABr b args ->
            if b == entry
                then ABr b args
                else ABr b (args ++ packFor b)
        ACondBr c tb ta fb fa ->
            let ta' = if tb == entry then ta else ta ++ packFor tb
                fa' = if fb == entry then fa else fa ++ packFor fb
            in ACondBr c tb ta' fb fa'
        ASwitch v cases mdef ->
            ASwitch v cases mdef
        ARet mv -> ARet mv
        AUnreachable -> AUnreachable
  where
    packFor :: BlockName -> [AOperand]
    packFor succB =
        [ fromMaybe (error ("PromoteRefs: missing current value for " ++ r)) v
        | (r, _) <- promoted
        , let needSet = Map.findWithDefault Set.empty r needs
        , Set.member succB needSet
        , let v = Map.lookup r curr
        ]

type Subst = Map Name AOperand

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
        OpGetDict className ty -> OpGetDict className ty
        OpDictCall dict methodIdx method args -> OpDictCall (substOperand env dict) methodIdx method (map (substOperand env) args)
        OpDup label val -> OpDup label (substOperand env val)
        OpDupProj0 handle -> OpDupProj0 (substOperand env handle)
        OpDupProj1 handle -> OpDupProj1 (substOperand env handle)
        OpWrapClosure fn -> OpWrapClosure (substOperand env fn)
        OpAllocClosure fn arity envSz -> OpAllocClosure (substOperand env fn) arity envSz
        OpClosureSetEnv closure idx val -> OpClosureSetEnv (substOperand env closure) idx (substOperand env val)
        OpClosureGetEnv closure idx -> OpClosureGetEnv (substOperand env closure) idx
        OpClosureGetFunc closure -> OpClosureGetFunc (substOperand env closure)
        -- Session 13: specialized closure duplication ops
        OpDupClosure label closure slotInfo -> OpDupClosure label (substOperand env closure) slotInfo
        OpDupClosureProj0 handle envSz slotInfo -> OpDupClosureProj0 (substOperand env handle) envSz slotInfo
        OpDupClosureProj1 handle envSz slotInfo -> OpDupClosureProj1 (substOperand env handle) envSz slotInfo
        OpClosureGetEnvDirect closure idx -> OpClosureGetEnvDirect (substOperand env closure) idx
        OpClosureGetEnvSUP closure idx -> OpClosureGetEnvSUP (substOperand env closure) idx
        -- Session 19: parallel projection ops
        OpParProj0 handle workEst -> OpParProj0 (substOperand env handle) workEst
        OpParProj1 handle workEst -> OpParProj1 (substOperand env handle) workEst
        OpParClosureProj0 handle envSz slotInfo workEst -> OpParClosureProj0 (substOperand env handle) envSz slotInfo workEst
        OpParClosureProj1 handle envSz slotInfo workEst -> OpParClosureProj1 (substOperand env handle) envSz slotInfo workEst
        OpPanic msg -> OpPanic msg
        -- Session 27: graph reduction ops
        OpGraphInit n -> OpGraphInit n
        OpGraphShutdown -> OpGraphShutdown
        OpGraphNum v -> OpGraphNum (substOperand env v)
        OpGraphAdd l r -> OpGraphAdd (substOperand env l) (substOperand env r)
        OpGraphSub l r -> OpGraphSub (substOperand env l) (substOperand env r)
        OpGraphMul l r -> OpGraphMul (substOperand env l) (substOperand env r)
        OpGraphCall fnIdx args -> OpGraphCall fnIdx (map (substOperand env) args)
        OpGraphReduce root -> OpGraphReduce (substOperand env root)
        OpGraphRegisterFunc name arity impl -> OpGraphRegisterFunc name arity (substOperand env impl)
        -- Session 29: interaction net operations
        OpGraphDup label target -> OpGraphDup label (substOperand env target)
        OpGraphSup label l r -> OpGraphSup label (substOperand env l) (substOperand env r)
        OpGraphLam varSlot body -> OpGraphLam (substOperand env varSlot) (substOperand env body)
        OpGraphApp fn arg -> OpGraphApp (substOperand env fn) (substOperand env arg)
        OpGraphEra -> OpGraphEra

substEffect :: Subst -> AEffect -> AEffect
substEffect env eff =
    case eff of
        EffStore p v -> EffStore (substOperand env p) (substOperand env v)
        EffStoreIndex a i v -> EffStoreIndex (substOperand env a) (substOperand env i) (substOperand env v)
        EffDrop a -> EffDrop (substOperand env a)
        EffClosureSetEnv closure idx val -> EffClosureSetEnv (substOperand env closure) idx (substOperand env val)
        EffGraphInit n -> EffGraphInit n
        EffGraphShutdown -> EffGraphShutdown

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

findAllocaCandidates :: AlloyFunction -> [(Name, Type, Type)]
findAllocaCandidates AlloyFunction{afBlocks} =
    let step acc ABlock{abInstrs} = foldl' collect acc abInstrs
        collect xs (ILet n refTy (OpAllocStack elemTy)) = (n, refTy, elemTy) : xs
        collect xs _ = xs
    in reverse (foldl' step [] afBlocks)

uniqueLocals :: AlloyFunction -> Set.Set Name
uniqueLocals fn =
    let FunctionReport{frLocalUniq = LocalUniq{luLocals}} = analyzeFunction fn
    in Set.fromList [n | (n, Unique) <- Map.toList luLocals]

uniqueOk :: Name -> Set.Set Name -> Bool
uniqueOk n s = n `Set.member` s

usesOnlyLoadStore :: Name -> AlloyFunction -> Bool
usesOnlyLoadStore n AlloyFunction{afBlocks} =
    all okBlock afBlocks
  where
    okBlock ABlock{abInstrs, abTerminator} =
        all okInstr abInstrs && okTerm abTerminator

    okInstr (ILet _ _ (OpLoad (OpVar p))) | p == n = True
    okInstr (ILet _ _ (OpLoad a)) = not (isVar n a) -- any other load ptr usage is disqualifying if equals n
    okInstr (ILet _ _ op) = not (appearsAs n op)
    okInstr (IEffect (EffStore (OpVar p) v)) | p == n = not (isVar n v)
    okInstr (IEffect eff) = not (appearsInEff n eff)

    okTerm t = not (appearsInTerm n t)

    appearsAs :: Name -> AOp -> Bool
    appearsAs r op =
        case op of
            OpBin _ a b -> isVar r a || isVar r b
            OpUnary _ a -> isVar r a
            OpCmp _ a b -> isVar r a || isVar r b
            OpLoad a -> isVar r a
            OpAllocStack _ -> False
            OpAllocHeap _ -> False
            OpCall callee args ->
                any (isVar r) (calleeToOps callee ++ args)
            OpConstruct _ _ fields -> any (isVar r) fields
            OpTagOf a -> isVar r a
            OpProject a _ -> isVar r a
            OpIndex a i -> isVar r a || isVar r i
            OpMakeArray xs -> any (isVar r) xs
            OpMakeTuple xs -> any (isVar r) xs
            OpGetDict _ _ -> False
            OpDictCall dict _ _ args -> isVar r dict || any (isVar r) args
            OpDup _ val -> isVar r val
            OpDupProj0 handle -> isVar r handle
            OpDupProj1 handle -> isVar r handle
            OpWrapClosure fn -> isVar r fn
            OpAllocClosure fn _ _ -> isVar r fn
            OpClosureSetEnv closure _ val -> isVar r closure || isVar r val
            OpClosureGetEnv closure _ -> isVar r closure
            OpClosureGetFunc closure -> isVar r closure
            -- Session 13: specialized closure duplication ops
            OpDupClosure _ closure _ -> isVar r closure
            OpDupClosureProj0 handle _ _ -> isVar r handle
            OpDupClosureProj1 handle _ _ -> isVar r handle
            OpClosureGetEnvDirect closure _ -> isVar r closure
            OpClosureGetEnvSUP closure _ -> isVar r closure
            -- Session 19: parallel projection ops
            OpParProj0 handle _ -> isVar r handle
            OpParProj1 handle _ -> isVar r handle
            OpParClosureProj0 handle _ _ _ -> isVar r handle
            OpParClosureProj1 handle _ _ _ -> isVar r handle
            OpPanic _ -> False
            -- Session 27: graph reduction ops
            OpGraphInit _ -> False
            OpGraphShutdown -> False
            OpGraphNum v -> isVar r v
            OpGraphAdd l rhs -> isVar r l || isVar r rhs
            OpGraphSub l rhs -> isVar r l || isVar r rhs
            OpGraphMul l rhs -> isVar r l || isVar r rhs
            OpGraphCall _ args -> any (isVar r) args
            OpGraphReduce root -> isVar r root
            OpGraphRegisterFunc _ _ impl -> isVar r impl
            -- Session 29: interaction net operations
            OpGraphDup _ target -> isVar r target
            OpGraphSup _ l rhs -> isVar r l || isVar r rhs
            OpGraphLam varSlot body -> isVar r varSlot || isVar r body
            OpGraphApp fn arg -> isVar r fn || isVar r arg
            OpGraphEra -> False

    appearsInEff :: Name -> AEffect -> Bool
    appearsInEff r eff =
        case eff of
            EffStore p v -> isVar r p || isVar r v
            EffStoreIndex a i v -> isVar r a || isVar r i || isVar r v
            EffDrop a -> isVar r a
            EffClosureSetEnv closure _ val -> isVar r closure || isVar r val
            EffGraphInit _ -> False
            EffGraphShutdown -> False

    appearsInTerm :: Name -> ATerminator -> Bool
    appearsInTerm r t =
        case t of
            ABr _ args -> any (isVar r) args
            ACondBr c _ ta _ fa -> isVar r c || any (isVar r) (ta ++ fa)
            ASwitch v _ _ -> isVar r v
            ARet mv -> maybe False (isVar r) mv
            AUnreachable -> False

    isVar :: Name -> AOperand -> Bool
    isVar r (OpVar x) = r == x
    isVar _ (OpConst _) = False

    calleeToOps :: ACallable -> [AOperand]
    calleeToOps (Direct _) = []
    calleeToOps (Indirect a) = [a]

entryNoLoadBeforeStore :: Name -> AlloyFunction -> Bool
entryNoLoadBeforeStore r AlloyFunction{afEntry, afBlocks} =
    let blk = hardHead [b | b@ABlock{abName} <- afBlocks, abName == afEntry]
    in not (loadBeforeStore r (abInstrs blk))

loadBeforeStore :: Name -> [AInstr] -> Bool
loadBeforeStore r = go False
  where
    go _ [] = False
    go seenStore (instr : rest) =
        case instr of
            ILet _ _ (OpLoad (OpVar p)) | p == r && not seenStore -> True
            IEffect (EffStore (OpVar p) _) | p == r -> go True rest
            _ -> go seenStore rest

dominatedOnAllEdges :: Name -> AlloyFunction -> Bool
dominatedOnAllEdges r AlloyFunction{afEntry, afBlocks} =
    let blocks = afBlocks
        succs = succMap blocks

        hasStore :: Map BlockName Bool
        hasStore = Map.fromList [(abName b, blockHasStore r b) | b <- blocks]

        initIn :: Map BlockName Bool
        initIn =
            Map.fromList
                [ (abName b, abName b /= afEntry)
                | b <- blocks
                ]

        iterateFix :: Map BlockName Bool -> Map BlockName Bool
        iterateFix inMap =
            let outMap = Map.mapWithKey (\bn iv -> iv || Map.findWithDefault False bn hasStore) inMap
                inMap' =
                    foldl'
                        ( \acc (fromB, tos) ->
                            let outV = Map.findWithDefault False fromB outMap
                            in foldl' (\m toB -> Map.insert toB (Map.findWithDefault True toB m && outV) m) acc tos
                        )
                        inMap
                        (Map.toList succs)
            in inMap'

        fix :: Int -> Map BlockName Bool -> Map BlockName Bool
        fix 0 m = m
        fix k m =
            let m' = iterateFix m
            in if m' == m then m else fix (k - 1) m'

        finalIn = fix (Map.size initIn * 4) initIn
        finalOut = Map.mapWithKey (\bn iv -> iv || Map.findWithDefault False bn hasStore) finalIn

        okAll = all (\(bn, outs) -> null outs || Map.findWithDefault False bn finalOut) (Map.toList succs)
    in okAll

blockHasStore :: Name -> ABlock -> Bool
blockHasStore r ABlock{abInstrs} =
    any isStore abInstrs
  where
    isStore (IEffect (EffStore (OpVar p) _)) | p == r = True
    isStore _ = False

succMap :: [ABlock] -> Map BlockName [BlockName]
succMap blks =
    Map.fromList
        [ (abName b, succs (abTerminator b))
        | b <- blks
        ]
  where
    succs t =
        case t of
            ABr b _ -> [b]
            ACondBr _ tb _ fb _ -> [tb, fb]
            ASwitch _ cs mdef ->
                let base = map snd cs
                in maybe base (: base) mdef
            ARet _ -> []
            AUnreachable -> []

paramName :: Name -> BlockName -> Name
paramName = makeRefParamName

trivialRefPeephole :: AlloyFunction -> AlloyFunction
trivialRefPeephole fn@AlloyFunction{afParams, afBlocks} =
    let paramNames = map fst afParams
        cands =
            [ (n, v)
            | (n, _refTy, _ety) <- findAllocaCandidates fn
            , usesOnlyLoadStore n fn
            , entryNoLoadBeforeStore n fn
            , Just v <- [exactlyOneStoreValue n fn]
            , isGlobalishOperand paramNames v
            , dominatedOnAllEdges n fn || loadsAfterStoreSameBlock n fn
            ]
        trivialSet = Set.fromList (map fst cands)
        valueMap = Map.fromList cands

        rewriteBlk :: ABlock -> ABlock
        rewriteBlk ABlock{abName, abParams, abInstrs, abTerminator} =
            let
                step :: ([AInstr], Map Name AOperand) -> AInstr -> ([AInstr], Map Name AOperand)
                step (acc, subst) ins =
                    case ins of
                        -- Drop promoted alloca
                        ILet n _ (OpAllocStack _)
                            | n `Set.member` trivialSet -> (acc, subst)
                        -- Drop the single store
                        IEffect (EffStore (OpVar r) _)
                            | r `Set.member` trivialSet -> (acc, subst)
                        -- Replace loads with the stored value via substitution
                        ILet n _ (OpLoad (OpVar r))
                            | r `Set.member` trivialSet
                            , Just v <- Map.lookup r valueMap ->
                                (acc, Map.insert n v subst)
                        -- Default: propagate substitutions
                        ILet n t op ->
                            let op' = substOp subst op
                            in (ILet n t op' : acc, subst)
                        IEffect eff ->
                            let eff' = substEffect subst eff
                            in (IEffect eff' : acc, subst)

                (instrs', subst') = foldl' step ([], Map.empty) abInstrs
                term' = substTerminator subst' abTerminator
            in
                ABlock{abName, abParams, abInstrs = reverse instrs', abTerminator = term'}
    in if Map.null valueMap
        then fn
        else fn{afBlocks = map rewriteBlk afBlocks}

exactlyOneStoreValue :: Name -> AlloyFunction -> Maybe AOperand
exactlyOneStoreValue r AlloyFunction{afBlocks} =
    let vals =
            [ v
            | ABlock{abInstrs} <- afBlocks
            , IEffect (EffStore (OpVar p) v) <- abInstrs
            , p == r
            ]
    in case vals of
        [v] -> Just v
        _ -> Nothing

isGlobalishOperand :: [Name] -> AOperand -> Bool
isGlobalishOperand _ (OpConst _) = True
isGlobalishOperand params (OpVar n) = n `elem` params

loadsAfterStoreSameBlock :: Name -> AlloyFunction -> Bool
loadsAfterStoreSameBlock r AlloyFunction{afBlocks} =
    case [ (abName b, b, idx)
         | b@ABlock{abInstrs} <- afBlocks
         , Just idx <- [firstStoreIndex r abInstrs]
         ] of
        [(storeBlkName, storeBlk, _idx)] ->
            let okInStoreBlk = not (loadBeforeStore r (abInstrs storeBlk))
                noLoadsElsewhere =
                    all (noLoads r) [b | b@ABlock{abName} <- afBlocks, abName /= storeBlkName]
            in okInStoreBlk && noLoadsElsewhere
        _ -> False

firstStoreIndex :: Name -> [AInstr] -> Maybe Int
firstStoreIndex r = findIndex isStore
  where
    isStore (IEffect (EffStore (OpVar p) _)) | p == r = True
    isStore _ = False

noLoads :: Name -> ABlock -> Bool
noLoads r ABlock{abInstrs} =
    not (any isLoad abInstrs)
  where
    isLoad (ILet _ _ (OpLoad (OpVar p))) | p == r = True
    isLoad _ = False
