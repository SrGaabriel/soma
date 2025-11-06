{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Alloy.Simplify (
    simplifyModule,
    simplifyFunction,
) where

import Alloy.Ir
import Data.List (elemIndex)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, mapMaybe)
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
            fnD = dropUnreachableBlocks fnC2
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
                Map.Map BlockName [BlockName] ->
                Map.Map BlockName (Map.Map Name Int) ->
                Map.Map BlockName (Map.Map Name Int) ->
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

            buildPreds :: [ABlock] -> Map.Map BlockName [BlockName]
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
                Map.Map BlockName [BlockName] ->
                Map.Map BlockName (Map.Map Name Int) ->
                Map.Map BlockName (Map.Map Name Int) ->
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
                incomingTag :: Int -> BlockName -> Maybe Int
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

                findBlock :: BlockName -> [ABlock] -> Maybe ABlock
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

            substOperand :: Map.Map Name AOperand -> AOperand -> AOperand

            substOperand env (OpVar n) = Map.findWithDefault (OpVar n) n env
            substOperand _ c@(OpConst _) = c

            substCallable :: Map.Map Name AOperand -> ACallable -> ACallable

            substCallable _ (Direct n) = Direct n
            substCallable env (Indirect a) = Indirect (substOperand env a)

            substOp :: Map.Map Name AOperand -> AOp -> AOp

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

            substEffect env eff =
                case eff of
                    EffStore p v -> EffStore (substOperand env p) (substOperand env v)
                    EffStoreIndex a i v -> EffStoreIndex (substOperand env a) (substOperand env i) (substOperand env v)
                    EffDrop a -> EffDrop (substOperand env a)

            substTerminator :: Map.Map Name AOperand -> ATerminator -> ATerminator
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
                    ASwitch v cases mdef -> ASwitch (substOperand env v) cases mdef
                    ARet mv -> ARet (fmap (substOperand env) mv)
                    AUnreachable -> AUnreachable

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

            unifyTarget :: [(Int, BlockName)] -> Maybe BlockName -> Maybe BlockName
            unifyTarget cases mdef =
                case cases of
                    [] -> Nothing
                    ((_, firstTgt) : rest) ->
                        if all (\(_, t) -> t == firstTgt) rest
                            then case mdef of
                                Nothing -> Just firstTgt
                                Just defTgt -> if defTgt == firstTgt then Just firstTgt else Nothing
                            else Nothing

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
                    let v' = substOpd subst v
                    in (IEffect (EffStore (OpVar r) v') : acc, Map.insert r v' storeMap, subst)
                ILet n _ (OpLoad (OpVar r))
                    | Just v <- Map.lookup r storeMap ->
                        (acc, storeMap, Map.insert n v subst)
                ILet n t op ->
                    let op' = substOpAll subst op
                    in (ILet n t op' : acc, storeMap, subst)
                IEffect eff ->
                    let eff' = substEffAll subst eff
                    in (IEffect eff' : acc, storeMap, subst)
        (instrs', _stores, substMap) = foldl step ([], Map.empty, Map.empty) abInstrs
        term' = substTerminator substMap abTerminator
    in ABlock{abName, abParams, abInstrs = reverse instrs', abTerminator = term'}
  where
    substOpd env (OpVar n) = Map.findWithDefault (OpVar n) n env
    substOpd _ c@(OpConst _) = c
    substCall _ (Direct n) = Direct n
    substCall env (Indirect a) = Indirect (substOpd env a)
    substOpAll env op =
        case op of
            OpBin k a b -> OpBin k (substOpd env a) (substOpd env b)
            OpUnary k a -> OpUnary k (substOpd env a)
            OpCmp k a b -> OpCmp k (substOpd env a) (substOpd env b)
            OpLoad a -> OpLoad (substOpd env a)
            OpAllocStack t -> OpAllocStack t
            OpAllocHeap t -> OpAllocHeap t
            OpCall callee args -> OpCall (substCall env callee) (map (substOpd env) args)
            OpConstruct tn tag fields -> OpConstruct tn tag (map (substOpd env) fields)
            OpTagOf a -> OpTagOf (substOpd env a)
            OpProject a i -> OpProject (substOpd env a) i
            OpIndex a i -> OpIndex (substOpd env a) (substOpd env i)
            OpMakeArray xs -> OpMakeArray (map (substOpd env) xs)
            OpMakeTuple xs -> OpMakeTuple (map (substOpd env) xs)
    substEffAll env eff =
        case eff of
            EffStore p v -> EffStore (substOpd env p) (substOpd env v)
            EffStoreIndex a i v -> EffStoreIndex (substOpd env a) (substOpd env i) (substOpd env v)
            EffDrop a -> EffDrop (substOpd env a)

    substTerminator :: Map.Map Name AOperand -> ATerminator -> ATerminator
    substTerminator env t =
        case t of
            ABr b args -> ABr b (map (substOpd env) args)
            ACondBr c tb ta fb fa ->
                ACondBr
                    (substOpd env c)
                    tb
                    (map (substOpd env) ta)
                    fb
                    (map (substOpd env) fa)
            ASwitch v cases mdef -> ASwitch (substOpd env v) cases mdef
            ARet mv -> ARet (fmap (substOpd env) mv)
            AUnreachable -> AUnreachable

fixpoint :: (Eq a) => (a -> a) -> a -> a
fixpoint f x =
    let x' = f x
    in if x' == x then x else fixpoint f x'

buildBlockMap :: [ABlock] -> Map.Map BlockName ABlock
buildBlockMap = Map.fromList . map (\b -> (abName b, b))

lookupBlock :: AlloyFunction -> BlockName -> Maybe ABlock
lookupBlock AlloyFunction{afBlocks} name = Map.lookup name (buildBlockMap afBlocks)

successors :: ATerminator -> [BlockName]
successors (ABr b _) = [b]
successors (ACondBr _ tb _ fb _) = [tb, fb]
successors (ASwitch _ cases mdef) =
    let xs = map snd cases
    in maybe xs (: xs) mdef
successors (ARet _) = []
successors AUnreachable = []

reachableBlocks :: AlloyFunction -> Set.Set BlockName
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
    isJoinRet :: ABlock -> Maybe (BlockName, Name)
    isJoinRet ABlock{abName, abParams = [(pName, _)], abInstrs = [], abTerminator = ARet (Just (OpVar v))}
        | pName == v = Just (abName, pName)
    isJoinRet _ = Nothing

    inlineOne :: AlloyFunction -> (BlockName, Name) -> AlloyFunction
    inlineOne fn' (jName, _pName) =
        let blocks' = map (rewritePred jName) (afBlocks fn')

            blocks'' =
                if afEntry fn' == jName
                    then blocks'
                    else filter ((/= jName) . abName) blocks'
        in fn'{afBlocks = blocks''}

    rewritePred :: BlockName -> ABlock -> ABlock
    rewritePred jName blk@ABlock{abTerminator} =
        blk{abTerminator = rewriteTerm abTerminator}
      where
        rewriteTerm (ABr b [arg]) | b == jName = ARet (Just arg)
        rewriteTerm t = t

inlineForwardBlocks :: AlloyFunction -> AlloyFunction
inlineForwardBlocks fn =
    let fwdBlocks = mapMaybe isForward (afBlocks fn)

        fwdBlocks' = filter (\(bn, _, _, _) -> bn /= afEntry fn) fwdBlocks
    in foldl' inlineOne fn fwdBlocks'
  where
    isForward :: ABlock -> Maybe (BlockName, [(Name, Type)], BlockName, [AOperand])
    isForward ABlock{abName, abParams, abInstrs = [], abTerminator = ABr tgt args} =
        Just (abName, abParams, tgt, args)
    isForward _ = Nothing

    inlineOne :: AlloyFunction -> (BlockName, [(Name, Type)], BlockName, [AOperand]) -> AlloyFunction
    inlineOne fn' (fName, params, tgtName, tgtArgs) =
        let paramNames = map fst params
            blocks' = map (rewritePred fName paramNames tgtName tgtArgs) (afBlocks fn')
            blocks'' = filter ((/= fName) . abName) blocks'
        in fn'{afBlocks = blocks''}

    rewritePred :: BlockName -> [Name] -> BlockName -> [AOperand] -> ABlock -> ABlock
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
        rewriteTerm t = t

    substOperand :: Map.Map Name AOperand -> AOperand -> AOperand
    substOperand env (OpVar n) = fromMaybe (OpVar n) (Map.lookup n env)
    substOperand _ c@(OpConst _) = c
