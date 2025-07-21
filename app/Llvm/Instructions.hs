module Llvm.Instructions where

import Llvm.Values (LlvmValue, getValueType)
import Llvm.Ir (IR (toLlvm))
import Data.List (intercalate)
import Llvm.Types (LlvmType)

data LlvmInstruction
    = LlvmAdd LlvmType LlvmValue LlvmValue
    | LlvmSub LlvmType LlvmValue LlvmValue
    | LlvmMul LlvmType LlvmValue LlvmValue
    | LlvmCall LlvmValue LlvmType [LlvmValue]
    | LlvmLoad LlvmValue
    | LlvmGep LlvmValue [LlvmValue]
    | LlvmICmpEq LlvmType LlvmValue LlvmValue
    deriving (Show, Eq)

data LlvmStatement
    = LlvmAssign String LlvmInstruction
    | LlvmStore LlvmValue LlvmValue
    | LlvmRet LlvmType (Maybe LlvmValue)
    | LlvmBr String
    | LlvmBrCond LlvmValue String String
    | LlvmLabel String
    deriving (Show, Eq)

instance IR LlvmInstruction where
    toLlvm (LlvmAdd typ lhs rhs) = "add " ++ toLlvm typ ++ " " ++ toLlvm lhs ++ ", " ++ toLlvm rhs
    toLlvm (LlvmSub typ lhs rhs) = "sub " ++ toLlvm typ ++ " " ++ toLlvm lhs ++ ", " ++ toLlvm rhs
    toLlvm (LlvmMul typ lhs rhs) = "mul " ++ toLlvm typ ++ " " ++ toLlvm lhs ++ ", " ++ toLlvm rhs
    toLlvm (LlvmCall callee retType args) = "call " ++ toLlvm retType ++ " " ++ toLlvm callee ++ "(" ++ intercalate "," (map (\val -> (toLlvm $ getValueType val) ++ " " ++ toLlvm val) args) ++ ")"
    toLlvm (LlvmLoad value) = "load " ++ toLlvm value
    toLlvm (LlvmGep base indices) = "getelementptr " ++ toLlvm base ++ ", " ++ unwords (map toLlvm indices)
    toLlvm (LlvmICmpEq typ lhs rhs) = "icmp eq " ++ toLlvm typ ++ " " ++ toLlvm lhs ++ ", " ++ toLlvm rhs

instance IR LlvmStatement where
    toLlvm (LlvmAssign name instr) = "%" ++ name ++ " = " ++ toLlvm instr
    toLlvm (LlvmStore value target) = "store " ++ toLlvm value ++ ", " ++ toLlvm target
    toLlvm (LlvmRet typ Nothing) = "ret " ++ toLlvm typ
    toLlvm (LlvmRet typ (Just value)) = "ret " ++ toLlvm typ ++ " " ++ toLlvm value
    toLlvm (LlvmBr label) = "br " ++ label
    toLlvm (LlvmBrCond cond trueLabel falseLabel) =
        "br " ++ toLlvm cond ++ ", label " ++ trueLabel ++ ", label " ++ falseLabel
    toLlvm (LlvmLabel label) = label ++ ":"