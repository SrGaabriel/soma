module Llvm.Instructions where

import Llvm.Values (LlvmValue)

data LlvmInstruction
    = LlvmAdd LlvmValue LlvmValue
    | LlvmSub LlvmValue LlvmValue
    | LlvmMul LlvmValue LlvmValue
    | LlvmCall String [LlvmValue]
    | LlvmLoad LlvmValue
    | LlvmGep LlvmValue [LlvmValue]
    deriving (Show, Eq)

data LlvmStatement
    = LlvmAssign String LlvmInstruction
    | LlvmStore LlvmValue LlvmValue
    | LlvmRet (Maybe LlvmValue)
    | LlvmBr String
    | LlvmBrCond LlvmValue String String
    | LlvmLabel String
    deriving (Show, Eq)