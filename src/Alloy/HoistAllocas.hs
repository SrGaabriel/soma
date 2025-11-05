{-# LANGUAGE NamedFieldPuns #-}

module Alloy.HoistAllocas (
    hoistAllocasModule,
    hoistAllocasFunction,
) where

import Alloy.Ir

hoistAllocasModule :: AlloyModule -> AlloyModule
hoistAllocasModule m@AlloyModule{amFunctions} =
    m{amFunctions = map hoistAllocasFunction amFunctions}

hoistAllocasFunction :: AlloyFunction -> AlloyFunction
hoistAllocasFunction fn@AlloyFunction{afEntry, afBlocks} =
    case splitAllBlocks afBlocks of
        (hoisted, stripped) ->
            let (before, entryBlk, after) = partitionAroundEntry afEntry stripped
                entryBlk' = prependAlloca hoisted entryBlk
            in fn{afBlocks = before ++ [entryBlk'] ++ after}

splitAllBlocks :: [ABlock] -> ([AInstr], [ABlock])
splitAllBlocks =
    foldr
        ( \blk (accAlloca, accBlocks) ->
            let (blkAlloca, blkStripped) = splitBlock blk
            in (blkAlloca ++ accAlloca, blkStripped : accBlocks)
        )
        ([], [])

splitBlock :: ABlock -> ([AInstr], ABlock)
splitBlock blk@ABlock{abInstrs} =
    let (allocas, others) = partitionAllocas abInstrs
    in (allocas, blk{abInstrs = others})

partitionAllocas :: [AInstr] -> ([AInstr], [AInstr])
partitionAllocas = go [] []
  where
    go as bs [] = (reverse as, reverse bs)
    go as bs (i:is) =
        case i of
            ILet _ _ (OpAllocStack _) -> go (i : as) bs is
            _ -> go as (i : bs) is

partitionAroundEntry :: BlockName -> [ABlock] -> ([ABlock], ABlock, [ABlock])
partitionAroundEntry entryName blks =
    let (prefix, rest) = break (\b -> abName b == entryName) blks
    in case rest of
        (e : suffix) -> (prefix, e, suffix)
        [] -> error "Alloy.HoistAllocas: Entry block not found"

prependAlloca :: [AInstr] -> ABlock -> ABlock
prependAlloca allocas blk@ABlock{abInstrs} =
    if null allocas
        then blk
        else blk{abInstrs = allocas ++ abInstrs}
