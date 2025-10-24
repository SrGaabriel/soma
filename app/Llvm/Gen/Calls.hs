module Llvm.Gen.Calls where

import Llvm.Gen.Context (GenValue, getGenValueType, mkDirectCall)
import Llvm.Gen.Core (IrGen, coerceArgsForCall, mkFnCall, saveInstruction)
import Llvm.Gen.Mangling (mangleInstanceMethod)
import Llvm.Types (LlvmType, normalizeType)
import Utils.Lists (hardHead)

mkTypeclassMethodCall :: String -> String -> [GenValue] -> [LlvmType] -> LlvmType -> IrGen GenValue
mkTypeclassMethodCall className methodName argVals expectedParamTypes llvmRetType = do
    let firstArgType = getGenValueType (hardHead argVals)
    let normalizedType = normalizeType firstArgType
    let mangledName = mangleInstanceMethod className normalizedType methodName

    coercedArgVals <- coerceArgsForCall argVals expectedParamTypes

    let callInstr = mkFnCall mangledName coercedArgVals llvmRetType
    mkDirectCall mangledName coercedArgVals llvmRetType
        <$> saveInstruction callInstr llvmRetType
