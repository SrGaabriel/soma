module Llvm.Values where

import Llvm.Types (LlvmType)

data LlvmValue
    = LlvmLiteral LlvmType String
    | LlvmRegister LlvmType String
    | LlvmGlobal LlvmType String
    | LlvmUndef LlvmType
    deriving (Show, Eq)

getRegName :: LlvmValue -> String
getRegName (LlvmRegister _ name) = name
getRegName _ = error "LlvmValue is not a register"