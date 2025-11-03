{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Alloy.Simplify (
    simplifyModule,
    simplifyFunction,
) where

import Alloy.Ir
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
            fnC = dropUnreachableBlocks fnB
        in fnC

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
dropUnreachableBlocks fn@AlloyFunction{afBlocks} =
    let rs = reachableBlocks fn
        bs' = filter (\b -> Set.member (abName b) rs) afBlocks
    in fn{afBlocks = bs'}

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
            blocks'' = filter ((/= jName) . abName) blocks'
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
    in foldl' inlineOne fn fwdBlocks
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
