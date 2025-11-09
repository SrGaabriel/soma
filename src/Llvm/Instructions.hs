module Llvm.Instructions where

import Data.List (intercalate)
import Llvm.Ir (IR (toLlvm))
import Llvm.Types (LlvmType, deref)
import Llvm.Values (LlvmValue, getValueType)

data LlvmInstruction
    = LlvmAdd LlvmType LlvmValue LlvmValue
    | LlvmSub LlvmType LlvmValue LlvmValue
    | LlvmMul LlvmType LlvmValue LlvmValue
    | LlvmCall LlvmValue LlvmType [LlvmValue]
    | LlvmLoad LlvmValue
    | LlvmAlloca LlvmType (Maybe LlvmValue)
    | LlvmICmp LlvmType String LlvmValue LlvmValue
    | LlvmGetElementPtr LlvmType LlvmValue [LlvmValue] Bool
    | LlvmBitcast LlvmValue LlvmType
    | LlvmExtractValue LlvmType LlvmValue Int
    | LlvmInsertValue LlvmType LlvmValue LlvmValue Int
    | LlvmPhi LlvmType [(LlvmValue, String)]
    | LlvmZExt LlvmValue LlvmType
    | LlvmSExt LlvmValue LlvmType
    | LlvmTrunc LlvmValue LlvmType
    | LlvmPtrToInt LlvmValue LlvmType
    | LlvmIntToPtr LlvmValue LlvmType
    | LlvmIdentityCast LlvmValue
    | LlvmTodoInstruction
    deriving (Show, Eq)

data LlvmStatement
    = LlvmAssign String LlvmInstruction
    | LlvmStore LlvmValue LlvmValue
    | LlvmRet LlvmType (Maybe LlvmValue)
    | LlvmBr String
    | LlvmBrCond LlvmValue String String
    | LlvmLabel String
    | LlvmCallStmt LlvmValue LlvmType [LlvmValue]
    | LlvmSwitch LlvmValue String [(LlvmValue, String)]
    | LlvmUnreachable
    | LlvmComment String
    deriving (Show, Eq)

instance IR LlvmInstruction where
    toLlvm (LlvmAdd typ lhs rhs) =
        "add " ++ toLlvm typ ++ " " ++ toLlvm lhs ++ ", " ++ toLlvm rhs
    toLlvm (LlvmSub typ lhs rhs) =
        "sub " ++ toLlvm typ ++ " " ++ toLlvm lhs ++ ", " ++ toLlvm rhs
    toLlvm (LlvmMul typ lhs rhs) =
        "mul " ++ toLlvm typ ++ " " ++ toLlvm lhs ++ ", " ++ toLlvm rhs
    toLlvm (LlvmCall callee retType args) =
        "call "
            ++ toLlvm retType
            ++ " "
            ++ toLlvm callee
            ++ "("
            ++ intercalate ", " (map (\v -> toLlvm (getValueType v) ++ " " ++ toLlvm v) args)
            ++ ")"
    toLlvm (LlvmLoad ptrVal) =
        "load " ++ toLlvm (deref $ getValueType ptrVal) ++ ", ptr " ++ toLlvm ptrVal
    toLlvm (LlvmAlloca ty Nothing) =
        "alloca " ++ toLlvm ty
    toLlvm (LlvmAlloca ty (Just count)) =
        "alloca " ++ toLlvm ty ++ ", " ++ toLlvm (getValueType count) ++ " " ++ toLlvm count
    toLlvm (LlvmICmp typ op lhs rhs) =
        "icmp " ++ op ++ " " ++ toLlvm typ ++ " " ++ toLlvm lhs ++ ", " ++ toLlvm rhs
    toLlvm (LlvmGetElementPtr structType basePtr indices inbounds) =
        "getelementptr "
            ++ (if inbounds then "inbounds " else "")
            ++ toLlvm structType
            ++ ", ptr "
            ++ toLlvm basePtr
            ++ concatMap (\idx -> ", " ++ toLlvm (getValueType idx) ++ " " ++ toLlvm idx) indices
    toLlvm (LlvmBitcast value targetType) =
        let sourceType = getValueType value
        in if sourceType == targetType
            -- todo: block identities to make things more strict
            then "select i1 true, " ++ toLlvm sourceType ++ " " ++ toLlvm value ++ ", " ++ toLlvm sourceType ++ " " ++ toLlvm value
            else "bitcast " ++ toLlvm sourceType ++ " " ++ toLlvm value ++ " to " ++ toLlvm targetType
    toLlvm (LlvmExtractValue structType value idx) =
        "extractvalue " ++ toLlvm structType ++ " " ++ toLlvm value ++ ", " ++ show idx
    toLlvm (LlvmInsertValue structType base new idx) =
        "insertvalue "
            ++ toLlvm structType
            ++ " "
            ++ toLlvm base
            ++ ", "
            ++ toLlvm (getValueType new)
            ++ " "
            ++ toLlvm new
            ++ ", "
            ++ show idx
    toLlvm (LlvmPhi typ incoming) =
        "phi "
            ++ toLlvm typ
            ++ " "
            ++ intercalate ", " (map (\(val, label) -> "[ " ++ toLlvm val ++ ", %" ++ label ++ " ]") incoming)
    toLlvm (LlvmZExt value targetType) =
        "zext " ++ toLlvm (getValueType value) ++ " " ++ toLlvm value ++ " to " ++ toLlvm targetType
    toLlvm (LlvmSExt value targetType) =
        "sext " ++ toLlvm (getValueType value) ++ " " ++ toLlvm value ++ " to " ++ toLlvm targetType
    toLlvm (LlvmTrunc value targetType) =
        "trunc " ++ toLlvm (getValueType value) ++ " " ++ toLlvm value ++ " to " ++ toLlvm targetType
    toLlvm (LlvmPtrToInt value targetType) =
        "ptrtoint " ++ toLlvm (getValueType value) ++ " " ++ toLlvm value ++ " to " ++ toLlvm targetType
    toLlvm (LlvmIntToPtr value targetType) =
        "inttoptr " ++ toLlvm (getValueType value) ++ " " ++ toLlvm value ++ " to " ++ toLlvm targetType
    toLlvm (LlvmIdentityCast value) =
        let ty = getValueType value
        in "select i1 true, " ++ toLlvm ty ++ " " ++ toLlvm value ++ ", " ++ toLlvm ty ++ " " ++ toLlvm value
    toLlvm LlvmTodoInstruction = "todo"

instance IR LlvmStatement where
    toLlvm (LlvmAssign name instr) =
        "%" ++ name ++ " = " ++ toLlvm instr
    toLlvm (LlvmStore value target) =
        "store " ++ toLlvm (getValueType value) ++ " " ++ toLlvm value ++ ", ptr " ++ toLlvm target
    toLlvm (LlvmRet typ Nothing) =
        "ret " ++ toLlvm typ
    toLlvm (LlvmRet typ (Just value)) =
        "ret " ++ toLlvm typ ++ " " ++ toLlvm value
    toLlvm (LlvmBr label) =
        "br label %" ++ label
    toLlvm (LlvmBrCond cond trueLabel falseLabel) =
        "br " ++ toLlvm (getValueType cond) ++ " " ++ toLlvm cond ++ ", label %" ++ trueLabel ++ ", label %" ++ falseLabel
    toLlvm (LlvmLabel label) =
        label ++ ":"
    toLlvm (LlvmCallStmt callee retType args) =
        "call "
            ++ toLlvm retType
            ++ " "
            ++ toLlvm callee
            ++ "("
            ++ intercalate ", " (map (\v -> toLlvm (getValueType v) ++ " " ++ toLlvm v) args)
            ++ ")"
    toLlvm (LlvmSwitch scrutinee defaultLabel cases) =
        "switch "
            ++ toLlvm (getValueType scrutinee)
            ++ " "
            ++ toLlvm scrutinee
            ++ ", label %"
            ++ defaultLabel
            ++ " ["
            ++ unwords (map (\(val, lbl) -> toLlvm (getValueType val) ++ " " ++ toLlvm val ++ ", label %" ++ lbl) cases)
            ++ "]"
    toLlvm LlvmUnreachable =
        "unreachable"
    toLlvm (LlvmComment comment) =
        "; " ++ comment
