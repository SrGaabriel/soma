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

getValueType :: LlvmValue -> LlvmType
getValueType (LlvmLiteral ty _) = ty
getValueType (LlvmRegister ty _) = ty
getValueType (LlvmGlobal ty _) = ty
getValueType (LlvmUndef ty) = ty