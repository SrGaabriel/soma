{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternSynonyms #-}

module Llvm.Types (
    LlvmType (..),
    pattern LlvmNamed,
    pattern LlvmStruct,
    pattern LlvmPtr,
    deref,
    llvmTypeSize,
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

deref :: LlvmType -> LlvmType
deref (LlvmPointer t) = t
deref u = error $ "Cannot dereference non-pointer type: " ++ show u

llvmTypeSize :: LlvmType -> Int
llvmTypeSize LlvmI1 = 1
llvmTypeSize LlvmI8 = 1
llvmTypeSize LlvmI16 = 2
llvmTypeSize LlvmI32 = 4
llvmTypeSize LlvmI64 = 8
llvmTypeSize LlvmFloat = 4
llvmTypeSize LlvmDouble = 8
llvmTypeSize (LlvmPointer _) = 8 -- todo: platform dependent pointer sizes
llvmTypeSize (LlvmArray n t) = n * llvmTypeSize t
llvmTypeSize (LlvmAnonymous ts) = sum (map llvmTypeSize ts)
llvmTypeSize _ = 8

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
