{-# LANGUAGE NamedFieldPuns #-}

module Llvm.Gen.OperandPass (buildOperandTypeEnv, OperandTypeEnv) where

import Alloy.Ir (
    ABlock (ABlock, abInstrs, abParams),
    AInstr (ILet),
    AlloyFunction (AlloyFunction, afBlocks, afParams),
    Name,
 )
import qualified Data.Map as Map
import Data.Set (Set)
import Llvm.Gen.TypeConversion (convertTypeWithStructInfo)
import Llvm.Types (LlvmType)
import Project.Unique (Unique)

type OperandTypeEnv = Map.Map Name LlvmType

buildOperandTypeEnv :: Set Unique -> Map.Map Unique String -> AlloyFunction -> OperandTypeEnv
buildOperandTypeEnv structs structNames AlloyFunction{afParams, afBlocks} =
    let conv = convertTypeWithStructInfo structs structNames
        fromParams = Map.fromList [(n, conv ty) | (n, ty) <- afParams]
        fromBlocks =
            foldl
                ( \acc ABlock{abParams, abInstrs} ->
                    let ps = Map.fromList [(n, conv ty) | (n, ty) <- abParams]
                        is = Map.fromList [(n, conv ty) | ILet n ty _ <- abInstrs]
                    in Map.unions [acc, ps, is]
                )
                Map.empty
                afBlocks
    in Map.unions [fromParams, fromBlocks]
