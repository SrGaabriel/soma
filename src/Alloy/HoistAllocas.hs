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
    let (hoisted, stripped) = splitAllBlocks afBlocks
        (before, entryBlk, after) = partitionAroundEntry afEntry stripped
        entryBlk' = prependAlloca hoisted entryBlk
    in fn{afBlocks = before ++ [entryBlk'] ++ after}

splitAllBlocks :: [ABlock] -> ([AInstr], [ABlock])
splitAllBlocks = foldr collectAllocas ([], [])
  where
    collectAllocas blk (accAlloca, accBlocks) =
        let (blkAlloca, blkStripped) = splitBlock blk
        in (blkAlloca ++ accAlloca, blkStripped : accBlocks)

splitBlock :: ABlock -> ([AInstr], ABlock)
splitBlock blk@ABlock{abInstrs} =
    let (allocas, others) = partitionAllocas abInstrs
    in (allocas, blk{abInstrs = others})

partitionAllocas :: [AInstr] -> ([AInstr], [AInstr])
partitionAllocas = go [] []
  where
    go allocas others [] = (reverse allocas, reverse others)
    go allocas others (i : is) =
        case i of
            ILet _ _ (OpAllocStack _) -> go (i : allocas) others is
            _ -> go allocas (i : others) is

partitionAroundEntry :: BlockName -> [ABlock] -> ([ABlock], ABlock, [ABlock])
partitionAroundEntry entryName blks =
    let (prefix, rest) = break (\b -> abName b == entryName) blks
    in case rest of
        (entry : suffix) -> (prefix, entry, suffix)
        [] -> error "Alloy.HoistAllocas: Entry block not found"

prependAlloca :: [AInstr] -> ABlock -> ABlock
prependAlloca [] blk = blk
prependAlloca allocas blk@ABlock{abInstrs} = blk{abInstrs = allocas ++ abInstrs}
