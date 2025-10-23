module Llvm.Gen.Calls where

import Llvm.Gen.Context (GenValue, mkDirectCall)
import Llvm.Gen.Core (IrGen, mkFnCall, saveInstruction)
import Llvm.Gen.Mangling (mangleInstanceMethod)
import Llvm.Types (LlvmType)

mkTypeclassMethodCall :: String -> String -> [GenValue] -> LlvmType -> IrGen GenValue
mkTypeclassMethodCall className methodName argVals llvmRetType = do
    let mangledName = mangleInstanceMethod className llvmRetType methodName
    let callInstr = mkFnCall mangledName argVals llvmRetType
    mkDirectCall mangledName argVals llvmRetType
        <$> saveInstruction callInstr llvmRetType
