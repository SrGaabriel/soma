{-# LANGUAGE NamedFieldPuns #-}

module Llvm.Gen.OperandPass (buildOperandTypeEnv, OperandTypeEnv) where

import Alloy.Ir (
    ABlock (ABlock, abInstrs, abParams),
    AInstr (ILet),
    AlloyFunction (AlloyFunction, afBlocks, afParams),
    Name,
 )
import qualified Data.Map as Map
import Llvm.Gen.TypeConversion (convertType)
import Llvm.Types (LlvmType)

type OperandTypeEnv = Map.Map Name LlvmType

buildOperandTypeEnv :: AlloyFunction -> OperandTypeEnv
buildOperandTypeEnv AlloyFunction{afParams, afBlocks} =
    let fromParams = Map.fromList [(n, convertType ty) | (n, ty) <- afParams]
        fromBlocks =
            foldl
                ( \acc ABlock{abParams, abInstrs} ->
                    let ps = Map.fromList [(n, convertType ty) | (n, ty) <- abParams]
                        is = Map.fromList [(n, convertType ty) | ILet n ty _ <- abInstrs]
                    in Map.unions [acc, ps, is]
                )
                Map.empty
                afBlocks
    in Map.unions [fromParams, fromBlocks]
