{-# LANGUAGE NamedFieldPuns #-}

module Llvm.Gen.OperandPass where

import Alloy.Ir
import qualified Data.Map as Map
import Llvm.Types

import Llvm.Gen.TypeConversion (convertType)

type OperandTypeEnv = Map.Map String LlvmType

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

lookupOperandType :: OperandTypeEnv -> AOperand -> Maybe LlvmType
lookupOperandType env (OpVar n) = Map.lookup n env
lookupOperandType _ _ = Nothing
