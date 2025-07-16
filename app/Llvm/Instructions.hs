module Llvm.Instructions where

import Llvm.Values (LlvmValue)
import Llvm.Ir (IR (toLlvm))

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

instance IR LlvmInstruction where
    toLlvm (LlvmAdd lhs rhs) = "add " ++ show lhs ++ ", " ++ show rhs
    toLlvm (LlvmSub lhs rhs) = "sub " ++ show lhs ++ ", " ++ show rhs
    toLlvm (LlvmMul lhs rhs) = "mul " ++ show lhs ++ ", " ++ show rhs
    toLlvm (LlvmCall name args) = "call " ++ name ++ "(" ++ unwords (map show args) ++ ")"
    toLlvm (LlvmLoad value) = "load " ++ show value
    toLlvm (LlvmGep base indices) = "getelementptr " ++ show base ++ ", " ++ unwords (map show indices)

instance IR LlvmStatement where
    toLlvm (LlvmAssign name instr) = name ++ " = " ++ toLlvm instr
    toLlvm (LlvmStore value target) = "store " ++ show value ++ ", " ++ show target
    toLlvm (LlvmRet Nothing) = "ret void"
    toLlvm (LlvmRet (Just value)) = "ret " ++ show value
    toLlvm (LlvmBr label) = "br " ++ label
    toLlvm (LlvmBrCond cond trueLabel falseLabel) =
        "br " ++ show cond ++ ", label " ++ trueLabel ++ ", label " ++ falseLabel
    toLlvm (LlvmLabel label) = label ++ ":"