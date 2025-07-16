module Llvm.Types where
import Llvm.Ir (IR (toLlvm))

data LlvmType
    = LlvmVoid
    | LlvmI1
    | LlvmI8
    | LlvmI16
    | LlvmI32
    | LlvmI64
    | LlvmFloat
    | LlvmDouble
    | LlvmPtr LlvmType
    | LlvmPointer LlvmType  -- Alternative pointer syntax
    | LlvmArray Int LlvmType
    | LlvmStruct String
    deriving (Show, Eq)

instance IR LlvmType where
    toLlvm LlvmVoid = "void"
    toLlvm LlvmI1 = "i1"
    toLlvm LlvmI8 = "i8"
    toLlvm LlvmI16 = "i16"
    toLlvm LlvmI32 = "i32"
    toLlvm LlvmI64 = "i64"
    toLlvm LlvmFloat = "float"
    toLlvm LlvmDouble = "double"
    toLlvm (LlvmPtr t) = toLlvm t ++ "*"
    toLlvm (LlvmPointer t) = toLlvm t ++ "*"
    toLlvm (LlvmArray n t) = "[" ++ show n ++ " x " ++ toLlvm t ++ "]"
    toLlvm (LlvmStruct name) = "%" ++ name