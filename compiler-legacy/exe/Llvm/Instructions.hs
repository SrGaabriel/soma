module Llvm.Instructions where

import Data.List (intercalate)
import Llvm.Ir (IR (toLlvm))
import Llvm.Types (LlvmType (..), deref)
import Llvm.Values (LlvmValue, getValueType)

data LlvmInstruction
    = LlvmAdd LlvmType LlvmValue LlvmValue
    | LlvmSub LlvmType LlvmValue LlvmValue
    | LlvmMul LlvmType LlvmValue LlvmValue
    | LlvmSDiv LlvmType LlvmValue LlvmValue
    | LlvmSRem LlvmType LlvmValue LlvmValue
    | LlvmAShr LlvmType LlvmValue LlvmValue
    | LlvmLShr LlvmType LlvmValue LlvmValue
    | LlvmShl LlvmType LlvmValue LlvmValue
    | LlvmAnd LlvmType LlvmValue LlvmValue
    | LlvmOr LlvmType LlvmValue LlvmValue
    | LlvmCall LlvmValue LlvmType [LlvmValue]
    | LlvmTailCall LlvmValue LlvmType [LlvmValue] -- tail call optimization
    | LlvmLoad LlvmValue
    | LlvmLoadTyped LlvmType LlvmValue -- explicit load type for opaque pointers
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
    | LlvmAtomicRmw String LlvmValue LlvmValue String -- op, ptr, val, ordering (e.g., "add", ptr, 1, "seq_cst")
    | LlvmSelect LlvmValue LlvmValue LlvmValue LlvmType -- cond, trueVal, falseVal, resultType
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
        "add nsw " ++ toLlvm typ ++ " " ++ toLlvm lhs ++ ", " ++ toLlvm rhs
    toLlvm (LlvmSub typ lhs rhs) =
        "sub nsw " ++ toLlvm typ ++ " " ++ toLlvm lhs ++ ", " ++ toLlvm rhs
    toLlvm (LlvmMul typ lhs rhs) =
        "mul nsw " ++ toLlvm typ ++ " " ++ toLlvm lhs ++ ", " ++ toLlvm rhs
    toLlvm (LlvmSDiv typ lhs rhs) =
        "sdiv " ++ toLlvm typ ++ " " ++ toLlvm lhs ++ ", " ++ toLlvm rhs
    toLlvm (LlvmSRem typ lhs rhs) =
        "srem " ++ toLlvm typ ++ " " ++ toLlvm lhs ++ ", " ++ toLlvm rhs
    toLlvm (LlvmAShr typ lhs rhs) =
        "ashr " ++ toLlvm typ ++ " " ++ toLlvm lhs ++ ", " ++ toLlvm rhs
    toLlvm (LlvmLShr typ lhs rhs) =
        "lshr " ++ toLlvm typ ++ " " ++ toLlvm lhs ++ ", " ++ toLlvm rhs
    toLlvm (LlvmShl typ lhs rhs) =
        "shl " ++ toLlvm typ ++ " " ++ toLlvm lhs ++ ", " ++ toLlvm rhs
    toLlvm (LlvmAnd typ lhs rhs) =
        "and " ++ toLlvm typ ++ " " ++ toLlvm lhs ++ ", " ++ toLlvm rhs
    toLlvm (LlvmOr typ lhs rhs) =
        "or " ++ toLlvm typ ++ " " ++ toLlvm lhs ++ ", " ++ toLlvm rhs
    toLlvm (LlvmCall callee retType args) =
        "call "
            ++ toLlvm retType
            ++ " "
            ++ toLlvm callee
            ++ "("
            ++ intercalate ", " (map (\v -> toLlvm (getValueType v) ++ " " ++ toLlvm v) args)
            ++ ")"
    toLlvm (LlvmTailCall callee retType args) =
        "tail call "
            ++ toLlvm retType
            ++ " "
            ++ toLlvm callee
            ++ "("
            ++ intercalate ", " (map (\v -> toLlvm (getValueType v) ++ " " ++ toLlvm v) args)
            ++ ")"
    toLlvm (LlvmLoad ptrVal) =
        "load " ++ toLlvm (deref $ getValueType ptrVal) ++ ", ptr " ++ toLlvm ptrVal
    toLlvm (LlvmLoadTyped loadTy ptrVal) =
        "load " ++ toLlvm loadTy ++ ", ptr " ++ toLlvm ptrVal
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
            -- Identity cast - use bitcast ptr to ptr for pointers, add 0 for integers
            then case sourceType of
                LlvmPointer _ -> "bitcast " ++ toLlvm sourceType ++ " " ++ toLlvm value ++ " to " ++ toLlvm targetType
                _ -> "add " ++ toLlvm sourceType ++ " " ++ toLlvm value ++ ", 0"
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
        -- identity cast - use appropriate no-op for the type
        let ty = getValueType value
        in case ty of
            LlvmPointer _ -> "bitcast " ++ toLlvm ty ++ " " ++ toLlvm value ++ " to " ++ toLlvm ty
            _ -> "add " ++ toLlvm ty ++ " " ++ toLlvm value ++ ", 0"
    toLlvm (LlvmAtomicRmw op ptrVal val ordering) =
        -- atomicrmw add ptr %ptr, i32 1 seq_cst
        "atomicrmw " ++ op ++ " ptr " ++ toLlvm ptrVal ++ ", " ++ toLlvm (getValueType val) ++ " " ++ toLlvm val ++ " " ++ ordering
    toLlvm (LlvmSelect cond trueVal falseVal ty) =
        -- select i1 %cond, i32 %true, i32 %false
        "select " ++ toLlvm (getValueType cond) ++ " " ++ toLlvm cond ++ ", " ++ toLlvm ty ++ " " ++ toLlvm trueVal ++ ", " ++ toLlvm ty ++ " " ++ toLlvm falseVal
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
