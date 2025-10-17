module Llvm.Values where

import Llvm.Types (LlvmType (LlvmI32))
import Llvm.Ir (IR (toLlvm))

data LlvmValue
    = LlvmLiteral LlvmType String
    | LlvmRegister LlvmType String
    | LlvmGlobal LlvmType String
    
    deriving (Show, Eq)

getRegName :: LlvmValue -> String
getRegName (LlvmRegister _ name) = name
getRegName _ = error "LlvmValue is not a register"

getValueType :: LlvmValue -> LlvmType
getValueType (LlvmLiteral ty _) = ty
getValueType (LlvmRegister ty _) = ty
getValueType (LlvmGlobal ty _) = ty

instance IR LlvmValue where
    toLlvm (LlvmLiteral _ val) = val
    toLlvm (LlvmRegister _ name) = "%" ++ name
    toLlvm (LlvmGlobal _ name) = "@" ++ name

intLiteral :: Int -> LlvmValue
intLiteral val = LlvmLiteral LlvmI32 (show val)