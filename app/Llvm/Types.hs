module Llvm.Types where

import Llvm.Ir (IR (toLlvm))
import Data.List (intercalate)

data LlvmType
    = LlvmVoid
    | LlvmI1
    | LlvmI8
    | LlvmI16
    | LlvmI32
    | LlvmI64
    | LlvmFloat
    | LlvmDouble
    | LlvmPointer LlvmType -- Alternative pointer syntax
    | LlvmArray Int LlvmType
    | LlvmNamedType String
    | LlvmFn LlvmType [LlvmType]
    | LlvmAnonymous [LlvmType]
    | LlvmVararg
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
    toLlvm (LlvmPointer _) = "ptr"
    toLlvm (LlvmArray n t) = "[" ++ show n ++ " x " ++ toLlvm t ++ "]"
    toLlvm (LlvmNamedType name) = "%" ++ name
    toLlvm (LlvmAnonymous types) = "{" ++ intercalate ", " (map toLlvm types) ++ "}"
    toLlvm (LlvmFn retType argTypes) =
        toLlvm retType ++ " (" ++ intercalate ", " (map toLlvm argTypes) ++ ")"
    toLlvm LlvmVararg = "..."

getLlvmTypeSize :: LlvmType -> Int
getLlvmTypeSize LlvmVoid = 0
getLlvmTypeSize LlvmI1 = 1
getLlvmTypeSize LlvmI8 = 1
getLlvmTypeSize LlvmI16 = 2
getLlvmTypeSize LlvmI32 = 4
getLlvmTypeSize LlvmI64 = 8
getLlvmTypeSize LlvmFloat = 4
getLlvmTypeSize LlvmDouble = 8
getLlvmTypeSize (LlvmPointer _) = 8
getLlvmTypeSize (LlvmArray n t) = n * getLlvmTypeSize t
getLlvmTypeSize (LlvmAnonymous types) = sum (map getLlvmTypeSize types)
getLlvmTypeSize (LlvmNamedType _) = error "Named types do not have a fixed size"
getLlvmTypeSize (LlvmFn _ _) = error "Function types do not have a fixed size"
getLlvmTypeSize LlvmVararg = error "Vararg types do not have a fixed size"

deref :: LlvmType -> LlvmType
deref (LlvmPointer t) = t
deref u = error $ "Cannot dereference non-pointer type: " ++ show u
