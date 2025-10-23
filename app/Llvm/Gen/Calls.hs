module Llvm.Gen.Calls where

import Llvm.Gen.Context (GenValue, mkDirectCall, getGenValueType)
import Llvm.Gen.Core (IrGen, mkFnCall, saveInstruction)
import Llvm.Gen.Mangling (mangleInstanceMethod)
import Llvm.Types (LlvmType, normalizeType)
import Utils.Lists (hardHead)

mkTypeclassMethodCall :: String -> String -> [GenValue] -> LlvmType -> IrGen GenValue
mkTypeclassMethodCall className methodName argVals llvmRetType = do
    let firstArgType = getGenValueType (hardHead argVals)
    let normalizedType = normalizeType firstArgType
    let mangledName = mangleInstanceMethod className normalizedType methodName
    let callInstr = mkFnCall mangledName argVals llvmRetType
    mkDirectCall mangledName argVals llvmRetType
        <$> saveInstruction callInstr llvmRetType