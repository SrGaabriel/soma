{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Llvm.Types where

import Data.Hashable (Hashable)
import Data.List (intercalate)
import GHC.Generics (Generic)
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
    | LlvmPointer LlvmType
    | LlvmArray Int LlvmType
    | LlvmNamedType String
    | LlvmFn LlvmType [LlvmType]
    | LlvmAnonymous [LlvmType]
    | LlvmVararg
    | LlvmSkolem -- only for prod usage
    deriving (Show, Eq, Generic, Hashable)

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
    toLlvm LlvmSkolem = error "Cannot convert LlvmSkolem to LLVM IR"

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
getLlvmTypeSize LlvmSkolem = error "Skolem types do not have a fixed size"

deref :: LlvmType -> LlvmType
deref (LlvmPointer t) = t
deref u = error $ "Cannot dereference non-pointer type: " ++ show u

normalizeType :: LlvmType -> LlvmType
normalizeType (LlvmPointer t) = t
normalizeType t = t

naturalAlignment :: LlvmType -> Int
naturalAlignment LlvmI1 = 1
naturalAlignment LlvmI8 = 1
naturalAlignment LlvmI16 = 2
naturalAlignment LlvmI32 = 4
naturalAlignment LlvmI64 = 8
naturalAlignment LlvmFloat = 4
naturalAlignment LlvmDouble = 8
naturalAlignment (LlvmPointer _) = 8
naturalAlignment (LlvmArray _ t) = naturalAlignment t
naturalAlignment (LlvmAnonymous ts) =
    case ts of
        [] -> 1
        _ -> maximum (map naturalAlignment ts)
naturalAlignment (LlvmNamedType _) = 8
naturalAlignment (LlvmFn _ _) = 8
naturalAlignment LlvmVararg = 8
naturalAlignment LlvmVoid = 1
naturalAlignment LlvmSkolem = 8
