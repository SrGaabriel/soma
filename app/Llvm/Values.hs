module Llvm.Values where

import Llvm.Ir (IR (toLlvm))
import Llvm.Types (LlvmType (LlvmI32, LlvmI64))

data LlvmValue
    = LlvmLiteral LlvmType String
    | LlvmRegister LlvmType String
    | LlvmGlobal LlvmType String
    | LlvmUndef
    deriving (Show, Eq)

getRegName :: LlvmValue -> String
getRegName (LlvmRegister _ name) = name
getRegName _ = error "LlvmValue is not a register"

getValueType :: LlvmValue -> LlvmType
getValueType (LlvmLiteral ty _) = ty
getValueType (LlvmRegister ty _) = ty
getValueType (LlvmGlobal ty _) = ty
getValueType LlvmUndef = error "LlvmUndef has no type"

instance IR LlvmValue where
    toLlvm (LlvmLiteral _ val) = val
    toLlvm (LlvmRegister _ name) = "%" ++ name
    toLlvm (LlvmGlobal _ name) = "@" ++ name
    toLlvm LlvmUndef = "undef"

intLiteral :: Int -> LlvmValue
intLiteral val = LlvmLiteral LlvmI32 (show val)

longLiteral :: Int -> LlvmValue
longLiteral val = LlvmLiteral LlvmI64 (show val)