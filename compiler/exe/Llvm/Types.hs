{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternSynonyms #-}

module Llvm.Types (
    LlvmType (..),
    pattern LlvmNamed,
    pattern LlvmStruct,
    pattern LlvmPtr,
    getLlvmTypeSize,
    deref,
    normalizeType,
    naturalAlignment,
    LlvmFnAttr (..),
    LlvmMemoryEffect (..),
    fnAttrToLlvm,
) where

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
    | LlvmFunctionPtr LlvmType [LlvmType] -- function pointer (ret type, param types)
    | LlvmAnonymous [LlvmType]
    | LlvmVararg
    | LlvmSkolem -- only for prod usage
    deriving (Show, Eq, Generic, Hashable)

-- Type aliases for clarity
pattern LlvmNamed :: String -> LlvmType
pattern LlvmNamed name = LlvmNamedType name

pattern LlvmStruct :: [LlvmType] -> LlvmType
pattern LlvmStruct fields = LlvmAnonymous fields

pattern LlvmPtr :: LlvmType
pattern LlvmPtr = LlvmPointer LlvmI8

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
    toLlvm (LlvmFunctionPtr retType argTypes) =
        toLlvm retType ++ " (" ++ intercalate ", " (map toLlvm argTypes) ++ ")*"
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
getLlvmTypeSize (LlvmFunctionPtr _ _) = 8 -- Function pointers are pointer-sized
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
naturalAlignment (LlvmFunctionPtr _ _) = 8
naturalAlignment LlvmVararg = 8
naturalAlignment LlvmVoid = 1
naturalAlignment LlvmSkolem = 8

data LlvmFnAttr
    = FnAttrNoUnwind
    | FnAttrNoSync
    | FnAttrNoFree
    | FnAttrWillReturn
    | FnAttrNoRecurse
    | FnAttrMustProgress
    | FnAttrMemory LlvmMemoryEffect
    | FnAttrNoInline
    | FnAttrAlwaysInline
    | FnAttrInlineHint
    | FnAttrOptSize
    | FnAttrMinSize
    | FnAttrCold
    | FnAttrHot
    deriving (Show, Eq, Generic, Hashable)

data LlvmMemoryEffect
    = MemNone
    | MemRead
    | MemWrite
    | MemReadWrite
    | MemArgMemOnly
    | MemArgMemRead
    | MemInaccessibleMemOnly
    deriving (Show, Eq, Generic, Hashable)

fnAttrToLlvm :: LlvmFnAttr -> String
fnAttrToLlvm FnAttrNoUnwind = "nounwind"
fnAttrToLlvm FnAttrNoSync = "nosync"
fnAttrToLlvm FnAttrNoFree = "nofree"
fnAttrToLlvm FnAttrWillReturn = "willreturn"
fnAttrToLlvm FnAttrNoRecurse = "norecurse"
fnAttrToLlvm FnAttrMustProgress = "mustprogress"
fnAttrToLlvm (FnAttrMemory eff) = "memory(" ++ memEffectToLlvm eff ++ ")"
fnAttrToLlvm FnAttrNoInline = "noinline"
fnAttrToLlvm FnAttrAlwaysInline = "alwaysinline"
fnAttrToLlvm FnAttrInlineHint = "inlinehint"
fnAttrToLlvm FnAttrOptSize = "optsize"
fnAttrToLlvm FnAttrMinSize = "minsize"
fnAttrToLlvm FnAttrCold = "cold"
fnAttrToLlvm FnAttrHot = "hot"

memEffectToLlvm :: LlvmMemoryEffect -> String
memEffectToLlvm MemNone = "none"
memEffectToLlvm MemRead = "read"
memEffectToLlvm MemWrite = "write"
memEffectToLlvm MemReadWrite = "readwrite"
memEffectToLlvm MemArgMemOnly = "argmem: readwrite"
memEffectToLlvm MemArgMemRead = "argmem: read"
memEffectToLlvm MemInaccessibleMemOnly = "inaccessiblemem: readwrite"
