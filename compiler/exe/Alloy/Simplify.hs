{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Alloy.Simplify (
    simplifyModule,
    simplifyFunction,
    forwardClosureEnvValuesModule,
) where

import Alloy.Ir
import Alloy.Subst (effectVars, opVars, operandVars, substEffect, substOp, substOperand, substTerminator, terminatorVars)
import Data.List (elemIndex)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import Typing.Types

simplifyModule :: AlloyModule -> AlloyModule
simplifyModule m@AlloyModule{amFunctions} =
    let fns' = map simplifyFunction amFunctions
    in m{amFunctions = fns'}

simplifyFunction :: AlloyFunction -> AlloyFunction
simplifyFunction fn0 =
    let fn1 = simplifyEntryForward fn0
    in fixpoint simplifyOnce fn1
  where
    simplifyOnce :: AlloyFunction -> AlloyFunction
    simplifyOnce fn =
        let fnA = inlineJoinReturnBlocks fn
            fnB = inlineForwardBlocks fnA
            fnB1 = foldLocalConstructAccesses fnB
            fnC = foldSwitchOnKnownTag fnB1
            fnC1 = canonicalizeSwitches fnC
            fnC2 = eliminateTrivialReadOnlyRefs fnC1
            fnC3 = eliminateDeadLets fnC2
            fnC4 = eliminateDeadClosures fnC3
            fnD = dropUnreachableBlocks fnC4
        in fnD
      where
        foldSwitchOnKnownTag :: AlloyFunction -> AlloyFunction
        foldSwitchOnKnownTag f@AlloyFunction{afBlocks} =
            let preds = buildPreds afBlocks
                conTagsPer =
                    Map.fromList
                        [ (abName b, constructTagMap (abInstrs b))
                        | b <- afBlocks
                        ]
                tagOfPer =
                    Map.fromList
                        [ (abName b, tagOfMap (constructTagMap (abInstrs b)) (abInstrs b))
                        | b <- afBlocks
                        ]
                bs' = map (foldBlock preds conTagsPer tagOfPer afBlocks) afBlocks
            in f{afBlocks = bs'}
          where
            foldBlock ::
                Map.Map Name [Name] ->
                Map.Map Name (Map.Map Name Int) ->
                Map.Map Name (Map.Map Name Int) ->
                [ABlock] ->
                ABlock ->
                ABlock
            foldBlock preds conTagsPer tagOfPer allBlocks blk@ABlock{abName = curName, abTerminator} =
                case abTerminator of
                    ASwitch op cases _mdef ->
                        case op of
                            OpConst (CInt k) ->
                                case lookup k cases of
                                    Just target -> blk{abTerminator = ABr target []}
                                    Nothing -> blk
                            OpVar tagVar ->
                                let localKnown = Map.lookup curName tagOfPer >>= \m -> Map.lookup tagVar m
                                    folded =
                                        case localKnown of
                                            Just k -> Just k
                                            Nothing -> knownFromParams preds conTagsPer tagOfPer allBlocks blk tagVar
                                in case folded of
                                    Just k ->
                                        case lookup k cases of
                                            Just target -> blk{abTerminator = ABr target []}
                                            Nothing -> blk
                                    Nothing -> blk
                            _ -> blk
                    _ -> blk

            buildPreds :: [ABlock] -> Map.Map Name [Name]
            buildPreds blks =
                let pairs =
                        [ (s, abName b)
                        | b <- blks
                        , s <- successors (abTerminator b)
                        ]
                in Map.fromListWith (++) [(s, [p]) | (s, p) <- pairs]

            constructTagMap :: [AInstr] -> Map.Map Name Int

            constructTagMap instrs =
                Map.fromList
                    [ (n, fromIntegral tag)
                    | ILet n _ (OpConstruct _ tag _) <- instrs
                    ]

            tagOfMap :: Map.Map Name Int -> [AInstr] -> Map.Map Name Int

            tagOfMap conTags instrs =
                Map.fromList
                    [ (n, t)
                    | ILet n _ (OpTagOf (OpVar c)) <- instrs
                    , Just t <- [Map.lookup c conTags]
                    ]

            -- If tagVar is a block parameter, examine predecessor edges.
            -- If every predecessor supplies an argument whose tag is known and all tags are equal, return that tag.
            knownFromParams ::
                Map.Map Name [Name] ->
                Map.Map Name (Map.Map Name Int) ->
                Map.Map Name (Map.Map Name Int) ->
                [ABlock] ->
                ABlock ->
                Name ->
                Maybe Int
            knownFromParams preds _conTagsPer tagOfPer allBlocks ABlock{abName = curName, abParams} tagVar =
                case elemIndex tagVar (map fst abParams) of
                    Nothing -> Nothing
                    Just idx ->
                        let ps = Map.findWithDefault [] curName preds
                            tags = map (incomingTag idx) ps
                        in allEqualJust tags
              where
                incomingTag :: Int -> Name -> Maybe Int
                incomingTag idx predName =
                    case findBlock predName allBlocks of
                        Nothing -> Nothing
                        Just pblk@ABlock{abTerminator} ->
                            case abTerminator of
                                ABr b args
                                    | b == curName
                                    , idx < length args ->
                                        tagOfOperand pblk (args !! idx)
                                ACondBr _ tb ta fb fa
                                    | tb == curName
                                    , idx < length ta ->
                                        tagOfOperand pblk (ta !! idx)
                                    | fb == curName
                                    , idx < length fa ->
                                        tagOfOperand pblk (fa !! idx)
                                _ -> Nothing

                tagOfOperand :: ABlock -> AOperand -> Maybe Int
                tagOfOperand pblk (OpVar v) =
                    Map.lookup (abName pblk) tagOfPer >>= \m -> Map.lookup v m
                tagOfOperand _ _ = Nothing

                findBlock :: Name -> [ABlock] -> Maybe ABlock
                findBlock nm blks =
                    case [b | b <- blks, abName b == nm] of
                        (b : _) -> Just b
                        [] -> Nothing

                allEqualJust :: [Maybe Int] -> Maybe Int
                allEqualJust xs =
                    case sequence xs of
                        Just (y : ys) | all (== y) ys -> Just y
                        _ -> Nothing

        foldLocalConstructAccesses :: AlloyFunction -> AlloyFunction
        foldLocalConstructAccesses f@AlloyFunction{afBlocks} =
            let bs' = map foldBlockLC afBlocks
            in f{afBlocks = bs'}
          where
            foldBlockLC :: ABlock -> ABlock
            foldBlockLC ABlock{abName, abParams, abInstrs, abTerminator} =
                let (instrs', _constructs, subst) = foldl step ([], Map.empty, Map.empty) abInstrs
                    term' = substTerminator subst abTerminator
                in ABlock{abName, abParams, abInstrs = reverse instrs', abTerminator = term'}

            step :: ([AInstr], Map.Map Name (String, Int, [AOperand]), Map.Map Name AOperand) -> AInstr -> ([AInstr], Map.Map Name (String, Int, [AOperand]), Map.Map Name AOperand)

            step (acc, ctors, subst) ins =
                case ins of
                    ILet n t (OpConstruct tn tag fields) ->
                        let fields' = map (substOperand subst) fields
                            ctors' = Map.insert n (tn, tag, fields') ctors
                        in (ILet n t (OpConstruct tn tag fields') : acc, ctors', subst)
                    -- Project from knon constructor: substitute field, drop ILet
                    ILet n _ (OpProject (OpVar v) idx)
                        | Just (_tn, _tag, fields) <- Map.lookup v ctors
                        , idx >= 0
                        , idx < length fields ->
                            let val = fields !! idx
                            in (acc, ctors, Map.insert n val subst)
                    -- Tag of known constructor: substitute constant, drop ILet
                    ILet n _ (OpTagOf (OpVar v))
                        | Just (_tn, tag, _fields) <- Map.lookup v ctors ->
                            (acc, ctors, Map.insert n (OpConst (CInt (fromIntegral tag))) subst)
                    -- Default: propagate substitutions
                    ILet n t op ->
                        let op' = substOp subst op
                        in (ILet n t op' : acc, ctors, subst)
                    IEffect eff ->
                        let eff' = substEffect subst eff
                        in (IEffect eff' : acc, ctors, subst)

        canonicalizeSwitches :: AlloyFunction -> AlloyFunction
        canonicalizeSwitches f@AlloyFunction{afBlocks} =
            let bs' = map canonBlock afBlocks
            in f{afBlocks = bs'}
          where
            canonBlock :: ABlock -> ABlock
            canonBlock blk@ABlock{abTerminator = ASwitch _ cases mdef} =
                case unifyTarget cases mdef of
                    Just tgt -> blk{abTerminator = ABr tgt []}
                    Nothing -> blk
            canonBlock blk = blk

            unifyTarget :: [(Int, Name)] -> Maybe Name -> Maybe Name
            unifyTarget cases mdef =
                case cases of
                    [] -> Nothing
                    ((_, firstTgt) : rest) ->
                        if all (\(_, t) -> t == firstTgt) rest
                            then case mdef of
                                Nothing -> Just firstTgt
                                Just defTgt -> if defTgt == firstTgt then Just firstTgt else Nothing
                            else Nothing

-- Eliminate dead let bindings: variables that are defined but never used
eliminateDeadLets :: AlloyFunction -> AlloyFunction
eliminateDeadLets f@AlloyFunction{afBlocks} =
    let
        -- Collect all used variables using imported functions from Alloy.Subst
        usedVars =
            Set.fromList
                [ n
                | ABlock{abInstrs, abTerminator} <- afBlocks
                , n <- concatMap instrVars abInstrs ++ terminatorVars abTerminator
                ]
          where
            instrVars (ILet _ _ op) = opVars op
            instrVars (IEffect eff) = effectVars eff

        -- Check if an op has side effects (can't be eliminated even if result unused)
        hasSideEffects op = case op of
            OpCall _ _ -> True -- Calls may have side effects
            OpDictCall{} -> True
            _ -> False

        -- Drop unused let bindings (unless they have side effects)
        dropDeadLet :: AInstr -> Maybe AInstr
        dropDeadLet (ILet n _ op)
            | not (Set.member n usedVars) && not (hasSideEffects op) = Nothing
        dropDeadLet i = Just i

        blocks' =
            [ blk{abInstrs = mapMaybe dropDeadLet (abInstrs blk)}
            | blk <- afBlocks
            ]
    in
        f{afBlocks = blocks'}

{- | Eliminate dead closures: closures that are allocated but never used
(not called, not returned, not stored in escaping locations).

Note: This uses specialized liveness analysis where:
- closure_set_env does NOT count as a use (it's just setup)
- EffDrop does NOT count as a use (it's just cleanup)
If a closure is only set up and dropped, we eliminate both.
-}
eliminateDeadClosures :: AlloyFunction -> AlloyFunction
eliminateDeadClosures f@AlloyFunction{afBlocks} =
    let
        -- Find all closure names that are actually used (not just set_env'd)
        usedClosures =
            Set.fromList
                [ n
                | ABlock{abInstrs, abTerminator} <- afBlocks
                , n <- concatMap closureUsedInInstr abInstrs ++ closureUsedInTerm abTerminator
                ]

        -- Special liveness for closures: closure_set_env doesn't count as a use
        closureUsedInInstr (ILet _ _ op) = closureUsedInOp op
        closureUsedInInstr (IEffect eff) = closureUsedInEffect eff

        closureUsedInOp op = case op of
            -- closure_set_env does NOT count as a use - it's setting up the closure
            OpClosureSetEnv{} -> []
            -- For other ops, use the generic opVars from Alloy.Subst
            _ -> opVars op

        closureUsedInEffect eff = case eff of
            -- closure_set_env: the closure isn't "used", but the value stored IS
            EffClosureSetEnv _ _ v -> operandVars v
            -- EffDrop does NOT count as a use
            EffDrop _ -> []
            -- For other effects, use generic effectVars
            _ -> effectVars eff

        closureUsedInTerm = terminatorVars

        -- Drop dead closure allocations, their set_env effects, and their drops
        dropDeadClosure :: AInstr -> Maybe AInstr
        dropDeadClosure (ILet n _ (OpAllocClosure{}))
            | not (Set.member n usedClosures) = Nothing
        dropDeadClosure (IEffect (EffClosureSetEnv (OpVar c) _ _))
            | not (Set.member c usedClosures) = Nothing
        dropDeadClosure (IEffect (EffDrop (OpVar c)))
            | not (Set.member c usedClosures) = Nothing
        dropDeadClosure i = Just i

        blocks' =
            [ blk{abInstrs = mapMaybe dropDeadClosure (abInstrs blk)}
            | blk <- afBlocks
            ]
    in
        f{afBlocks = blocks'}

-- Eliminate trivial read-only refs after previous simplifications:
-- 1) Replace loads that occur after a store in the same block with the stored value
-- 2) Drop stores to pointers that are never loaded anywhere
-- 3) Drop allocas whose pointers are neither loaded nor stored anymore
eliminateTrivialReadOnlyRefs :: AlloyFunction -> AlloyFunction
eliminateTrivialReadOnlyRefs f@AlloyFunction{afBlocks} =
    let blocks1 = map replaceLoadsAfterStores afBlocks
        keepLoadPtrs =
            Set.fromList
                [ r
                | ABlock{abInstrs} <- blocks1
                , ILet _ _ (OpLoad (OpVar r)) <- abInstrs
                ]

        dropDeadStore :: AInstr -> Maybe AInstr
        dropDeadStore (IEffect (EffStore (OpVar r) _)) | not (Set.member r keepLoadPtrs) = Nothing
        dropDeadStore i = Just i

        blocks2 =
            [ blk{abInstrs = mapMaybe dropDeadStore (abInstrs blk)}
            | blk <- blocks1
            ]

        keepPtrs =
            Set.fromList
                [ r
                | ABlock{abInstrs} <- blocks2
                , instr <- abInstrs
                , r <- case instr of
                    ILet _ _ (OpLoad (OpVar p)) -> [p]
                    IEffect (EffStore (OpVar p) _) -> [p]
                    _ -> []
                ]

        dropDeadAlloca :: AInstr -> Maybe AInstr
        dropDeadAlloca (ILet n _ (OpAllocStack _)) | not (Set.member n keepPtrs) = Nothing
        dropDeadAlloca i = Just i

        blocks3 =
            [ blk{abInstrs = mapMaybe dropDeadAlloca (abInstrs blk)}
            | blk <- blocks2
            ]
    in f{afBlocks = blocks3}

replaceLoadsAfterStores :: ABlock -> ABlock
replaceLoadsAfterStores ABlock{abName, abParams, abInstrs, abTerminator} =
    let step (acc, storeMap, subst) ins =
            case ins of
                IEffect (EffStore (OpVar r) v) ->
                    let v' = substOperand subst v
                    in (IEffect (EffStore (OpVar r) v') : acc, Map.insert r v' storeMap, subst)
                ILet n _ (OpLoad (OpVar r))
                    | Just v <- Map.lookup r storeMap ->
                        (acc, storeMap, Map.insert n v subst)
                ILet n t op ->
                    let op' = substOp subst op
                    in (ILet n t op' : acc, storeMap, subst)
                IEffect eff ->
                    let eff' = substEffect subst eff
                    in (IEffect eff' : acc, storeMap, subst)
        (instrs', _stores, substMap) = foldl step ([], Map.empty, Map.empty) abInstrs
        term' = substTerminator substMap abTerminator
    in ABlock{abName, abParams, abInstrs = reverse instrs', abTerminator = term'}

-- | Forward closure environment values at module level
forwardClosureEnvValuesModule :: AlloyModule -> AlloyModule
forwardClosureEnvValuesModule m@AlloyModule{amFunctions} =
    m{amFunctions = map forwardClosureEnvValues amFunctions}

{- | Forward closure environment values: replace closure_get_env with the value
that was stored via closure_set_env, eliminating redundant env access.
This is crucial for optimizing inlined closure calls.
-}
forwardClosureEnvValues :: AlloyFunction -> AlloyFunction
forwardClosureEnvValues f@AlloyFunction{afBlocks} =
    f{afBlocks = map forwardInBlock afBlocks}
  where
    forwardInBlock :: ABlock -> ABlock
    forwardInBlock blk@ABlock{abInstrs, abTerminator} =
        let (instrs', _envMap, subst) = foldl step ([], Map.empty, Map.empty) abInstrs
            term' = substTerminator subst abTerminator
        in blk{abInstrs = reverse instrs', abTerminator = term'}

    -- Map from (closure_name, index) -> stored value
    -- EnvMap = Map.Map (Name, Int) AOperand

    step :: ([AInstr], Map.Map (Name, Int) AOperand, Map.Map Name AOperand) -> AInstr -> ([AInstr], Map.Map (Name, Int) AOperand, Map.Map Name AOperand)
    step (acc, envMap, subst) instr =
        case instr of
            -- Track closure_set_env: record the value stored at each slot
            IEffect (EffClosureSetEnv (OpVar closureName) idx val) ->
                let val' = substOperand subst val
                    envMap' = Map.insert (closureName, idx) val' envMap
                in (IEffect (EffClosureSetEnv (OpVar closureName) idx val') : acc, envMap', subst)
            -- Forward closure_get_env: if we know the value, substitute it
            ILet name _ (OpClosureGetEnv (OpVar closureName) idx) ->
                case Map.lookup (closureName, idx) envMap of
                    Just val ->
                        -- We know the value - don't emit the get, just substitute
                        (acc, envMap, Map.insert name val subst)
                    Nothing ->
                        -- Unknown - keep the instruction
                        (instr : acc, envMap, subst)
            -- For other ILet, apply substitution to the operands
            ILet name ty op ->
                let op' = substOp subst op
                in (ILet name ty op' : acc, envMap, subst)
            -- For effects, apply substitution
            IEffect eff ->
                let eff' = substEffect subst eff
                in (IEffect eff' : acc, envMap, subst)

fixpoint :: (Eq a) => (a -> a) -> a -> a
fixpoint f x =
    let x' = f x
    in if x' == x then x else fixpoint f x'

buildBlockMap :: [ABlock] -> Map.Map Name ABlock
buildBlockMap = Map.fromList . map (\b -> (abName b, b))

lookupBlock :: AlloyFunction -> Name -> Maybe ABlock
lookupBlock AlloyFunction{afBlocks} name = Map.lookup name (buildBlockMap afBlocks)

successors :: ATerminator -> [Name]
successors (ABr b _) = [b]
successors (ACondBr _ tb _ fb _) = [tb, fb]
successors (ASwitch _ cases mdef) =
    let xs = map snd cases
    in maybe xs (: xs) mdef
successors (ARet _) = []
successors AUnreachable = []

reachableBlocks :: AlloyFunction -> Set.Set Name
reachableBlocks AlloyFunction{afEntry, afBlocks} =
    let m = buildBlockMap afBlocks
        go seen [] = seen
        go seen (x : xs)
            | Set.member x seen = go seen xs
            | otherwise =
                case Map.lookup x m of
                    Nothing -> go seen xs
                    Just ABlock{abTerminator} ->
                        let ns = successors abTerminator
                        in go (Set.insert x seen) (ns ++ xs)
    in go Set.empty [afEntry]

dropUnreachableBlocks :: AlloyFunction -> AlloyFunction
dropUnreachableBlocks fn@AlloyFunction{afEntry, afBlocks} =
    let rs = reachableBlocks fn
        bs' = filter (\b -> Set.member (abName b) rs) afBlocks
        bs'' =
            if null bs' || not (any (\b -> abName b == afEntry) bs')
                then afBlocks
                else bs'
    in fn{afBlocks = bs''}

simplifyEntryForward :: AlloyFunction -> AlloyFunction
simplifyEntryForward fn@AlloyFunction{afEntry} =
    case lookupBlock fn afEntry of
        Just blk
            | isTrivialForwardEntry blk ->
                let ABlock{abTerminator = ABr target []} = blk
                    afBlocks' = filter ((/= abName blk) . abName) (afBlocks fn)
                in fn{afEntry = target, afBlocks = afBlocks'}
        _ -> fn
  where
    isTrivialForwardEntry :: ABlock -> Bool
    isTrivialForwardEntry ABlock{abParams, abInstrs, abTerminator} =
        null abParams
            && null abInstrs
            && case abTerminator of
                ABr _ args -> null args
                _ -> False

inlineJoinReturnBlocks :: AlloyFunction -> AlloyFunction
inlineJoinReturnBlocks fn =
    let joinBlocks = mapMaybe isJoinRet (afBlocks fn)
    in foldl' inlineOne fn joinBlocks
  where
    isJoinRet :: ABlock -> Maybe (Name, Name)
    isJoinRet ABlock{abName, abParams = [(pName, _)], abInstrs = [], abTerminator = ARet (Just (OpVar v))}
        | pName == v = Just (abName, pName)
    isJoinRet _ = Nothing

    inlineOne :: AlloyFunction -> (Name, Name) -> AlloyFunction
    inlineOne fn' (jName, _pName) =
        let blocks' = map (rewritePred jName) (afBlocks fn')

            blocks'' =
                if afEntry fn' == jName
                    then blocks'
                    else filter ((/= jName) . abName) blocks'
        in fn'{afBlocks = blocks''}

    rewritePred :: Name -> ABlock -> ABlock
    rewritePred jName blk@ABlock{abTerminator} =
        blk{abTerminator = rewriteTerm abTerminator}
      where
        rewriteTerm (ABr b [arg]) | b == jName = ARet (Just arg)
        rewriteTerm t = t

inlineForwardBlocks :: AlloyFunction -> AlloyFunction
inlineForwardBlocks fn =
    let fwdBlocks = mapMaybe isForward (afBlocks fn)

        fwdBlocks' = filter (\(bn, _, _, _) -> bn /= afEntry fn) fwdBlocks

        -- Check if there are any switches in the function
        hasSwitch = any blockHasSwitch (afBlocks fn)
        blockHasSwitch ABlock{abTerminator = ASwitch{}} = True
        blockHasSwitch _ = False
    in foldl' (inlineOne hasSwitch) fn fwdBlocks'
  where
    isForward :: ABlock -> Maybe (Name, [(Name, Type)], Name, [AOperand])
    isForward ABlock{abName, abParams, abInstrs = [], abTerminator = ABr tgt args} =
        Just (abName, abParams, tgt, args)
    isForward _ = Nothing

    inlineOne :: Bool -> AlloyFunction -> (Name, [(Name, Type)], Name, [AOperand]) -> AlloyFunction
    inlineOne hasSwitch fn' (fName, params, tgtName, tgtArgs) =
        let paramNames = map fst params
            -- If there are switches and the target has parameters (tgtArgs not empty),
            -- we can't safely inline because switches can't pass arguments.
            -- In this case, check if any switch actually references this block.
            canRemoveBlock = not hasSwitch || null tgtArgs || not (anyBlockRefersViaSwitchTo fName (afBlocks fn'))
            blocks' = map (rewritePred fName paramNames tgtName tgtArgs) (afBlocks fn')
            blocks'' =
                if canRemoveBlock
                    then filter ((/= fName) . abName) blocks'
                    else blocks'
        in fn'{afBlocks = blocks''}

    anyBlockRefersViaSwitchTo :: Name -> [ABlock] -> Bool
    anyBlockRefersViaSwitchTo targetName = any (switchRefersTo targetName . abTerminator)

    switchRefersTo :: Name -> ATerminator -> Bool
    switchRefersTo targetName (ASwitch _ cases mdef) =
        any ((== targetName) . snd) cases || mdef == Just targetName
    switchRefersTo _ _ = False

    rewritePred :: Name -> [Name] -> Name -> [AOperand] -> ABlock -> ABlock
    rewritePred fName pNames tgtName tgtArgs blk@ABlock{abTerminator} =
        blk{abTerminator = rewriteTerm abTerminator}
      where
        rewriteTerm (ABr b callArgs)
            | b == fName =
                let subst = Map.fromList (zip pNames callArgs)
                    newArgs = map (substOperand subst) tgtArgs
                in ABr tgtName newArgs
        rewriteTerm (ACondBr c tb ta fb fa) =
            let (tb', ta') =
                    if tb == fName
                        then
                            let subst = Map.fromList (zip pNames ta)
                                newArgs = map (substOperand subst) tgtArgs
                            in (tgtName, newArgs)
                        else (tb, ta)
                (fb', fa') =
                    if fb == fName
                        then
                            let subst = Map.fromList (zip pNames fa)
                                newArgs = map (substOperand subst) tgtArgs
                            in (tgtName, newArgs)
                        else (fb, fa)
            in ACondBr c tb' ta' fb' fa'
        -- Handle ASwitch: rewrite case targets that point to the forward block
        -- Note: switches don't pass arguments, so we can only inline forward blocks
        -- when BOTH the forward block has no parameters AND the target block has no parameters
        -- (i.e., tgtArgs is empty, meaning nothing needs to be passed to the target)
        rewriteTerm (ASwitch op cases mdef)
            | null pNames && null tgtArgs =
                -- Both forward block and target have no parameters, safe to redirect
                let cases' = map (\(tag, tgt) -> if tgt == fName then (tag, tgtName) else (tag, tgt)) cases
                    mdef' = fmap (\tgt -> if tgt == fName then tgtName else tgt) mdef
                in ASwitch op cases' mdef'
        rewriteTerm t = t
