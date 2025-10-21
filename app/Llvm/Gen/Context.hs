module Llvm.Gen.Context where

import Llvm.Types (LlvmType)
import Llvm.Values (LlvmValue, getValueType, intLiteral, longLiteral)

data GenValue = Contextualized
    { genValueContext :: GenCtx
    , gvw :: LlvmValue
    }
    deriving (Show, Eq)

data GenCtx
    = LiteralValue LitCtx
    | FunctionArg
    | MemoryAllocation MemAllocCtx
    | MemoryAccess MemAccessCtx
    | FunctionCall FunctionCallCtx
    | ValueLoad LoadCtx
    | ArrayOperation ArrayOpCtx
    deriving (Show, Eq)

data LitCtx
    = StringLit
    | NumLit
    | BoolLit
    deriving (Show, Eq)

data MemAllocCtx
    = StackStructAlloc
    | StackArrayAlloc
    | HeapAlloc
    deriving (Show, Eq)

data MemAccessCtx
    = ADTTagAccess
    | ADTUnionDataAccess
    | StructFieldAccess
    | ArrayElementAccess
    | ArrayHeaderOffset
    deriving (Show, Eq)

data FunctionCallCtx
    = DirectCall
    | IndirectCall
    deriving (Show, Eq)

data LoadCtx
    = StructValueLoad
    | ArrayElementLoad
    | VariableLoad
    | FieldLoad
    deriving (Show, Eq)

data ArrayOpCtx
    = SliceConstruction
    | SliceDeconstruction
    deriving (Show, Eq)

getGenValueType :: GenValue -> LlvmType
getGenValueType (Contextualized _ raw) = getValueType raw

cIntLiteral :: Int -> GenValue
cIntLiteral = Contextualized (LiteralValue NumLit) . intLiteral

cLongLiteral :: Int -> GenValue
cLongLiteral = Contextualized (LiteralValue NumLit) . longLiteral
