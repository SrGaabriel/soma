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
        { argPosition :: Int
        , argFunctionName :: Maybe String
        }
    | MemoryAllocation MemAllocCtx
    | MemoryAccess MemAccessCtx
    | FunctionCall FunctionCallCtx
    | ValueLoad LoadCtx
    | ArrayOperation ArrayOpCtx
    | ArithmeticOp ArithOpCtx
    | ComparisonOp CmpOpCtx
    | TypeConversion ConversionCtx
    | StructOperation StructOpCtx
    deriving (Show, Eq)

data LitCtx
    = StringLit
    | NumLit
    | BoolLit
    deriving (Show, Eq)

data MemAllocCtx
    = StackStructAlloc
        { allocatedType :: LlvmType
        }
    | StackArrayAlloc
        { allocatedType :: LlvmType
        , arraySize :: Maybe Int
        }
    | HeapAlloc
        { allocatedType :: LlvmType
        , heapSize :: Int
        }
    | LambdaPtrAlloc
        { lambdaFunctionName :: String
        }
    deriving (Show, Eq)

data MemAccessCtx
    = ADTTagAccess
        { basePointer :: GenValue
        }
    | ADTUnionDataAccess
        { basePointer :: GenValue
        }
    | StructFieldAccess
        { basePointer :: GenValue
        , structFieldIndex :: Int
        }
    | ArrayElementAccess
        { arrayPointer :: GenValue
        , indexValue :: GenValue
        }
    | ArrayHeaderOffset
        { rawPointer :: GenValue
        }
    | GlobalConstantAccess
        { globalName :: String
        , globalType :: LlvmType
        , indices :: [Int]
        , inbounds :: Bool
        }
    deriving (Show, Eq)

data FunctionCallCtx
    = DirectCall
        { calledFunction :: String
        , callArguments :: [GenValue]
        }
    | IndirectCall
        { functionPointer :: GenValue
        , callArguments :: [GenValue]
        }
    deriving (Show, Eq)

data LoadCtx
    = StructValueLoad
        { sourcePointer :: GenValue
        }
    | ArrayElementLoad
        { sourcePointer :: GenValue
        , elementIndex :: GenValue
        }
    | VariableLoad
        { sourcePointer :: GenValue
        , variableName :: Maybe String
        }
    | FieldLoad
        { sourcePointer :: GenValue
        , loadFieldIndex :: Int
        }
    deriving (Show, Eq)

data ArrayOpCtx
    = SliceConstruction
        { sliceDataPtr :: GenValue
        , sliceLength :: Int
        }
    | SliceDeconstruction
        { originalSlice :: Maybe GenValue
        }
    deriving (Show, Eq)

data ArithOpCtx
    = BinaryArith
        { arithOperation :: String -- "add", "sub", "mul", "div", "mod"
        , leftOperand :: GenValue
        , rightOperand :: GenValue
        }
    | UnaryArith
        { arithOperation :: String -- "neg" or "not"
        , operand :: GenValue
        }
    deriving (Show, Eq)

data CmpOpCtx
    = Comparison
    { comparisonOp :: String
    , cmpLeftOperand :: GenValue
    , cmpRightOperand :: GenValue
    }
    deriving (Show, Eq)

data ConversionCtx
    = Bitcast
        { sourceValue :: GenValue
        , targetType :: LlvmType
        }
    | IntToPtr
        { sourceValue :: GenValue
        , targetType :: LlvmType
        }
    | PtrToInt
        { sourceValue :: GenValue
        , targetType :: LlvmType
        }
    | Truncate
        { sourceValue :: GenValue
        , targetType :: LlvmType
        }
    | Extend
        { sourceValue :: GenValue
        , targetType :: LlvmType
        , isSigned :: Bool
        }
    deriving (Show, Eq)

data StructOpCtx
    = InsertValue
        { targetStruct :: Maybe GenValue
        , insertedValue :: GenValue
        , insertIndex :: Int
        }
    | ExtractValue
        { sourceStruct :: GenValue
        , extractIndex :: Int
        }
    deriving (Show, Eq)

getGenValueType :: GenValue -> LlvmType
getGenValueType (Contextualized _ raw) = getValueType raw

cIntLiteral :: Int -> GenValue
cIntLiteral = Contextualized (LiteralValue NumLit) . intLiteral

cLongLiteral :: Int -> GenValue
cLongLiteral = Contextualized (LiteralValue NumLit) . longLiteral

mkFunctionArg :: Int -> Maybe String -> LlvmValue -> GenValue
mkFunctionArg pos fname = Contextualized (FunctionArg pos fname)

mkStackStructAlloc :: LlvmType -> LlvmValue -> GenValue
mkStackStructAlloc ty = Contextualized (MemoryAllocation (StackStructAlloc ty))

mkStackArrayAlloc :: LlvmType -> Maybe Int -> LlvmValue -> GenValue
mkStackArrayAlloc ty size = Contextualized (MemoryAllocation (StackArrayAlloc ty size))

mkHeapAlloc :: LlvmType -> Int -> LlvmValue -> GenValue
mkHeapAlloc ty size = Contextualized (MemoryAllocation (HeapAlloc ty size))

mkLambdaPtrAlloc :: String -> LlvmValue -> GenValue
mkLambdaPtrAlloc fname = Contextualized (MemoryAllocation (LambdaPtrAlloc fname))

mkADTTagAccess :: GenValue -> LlvmValue -> GenValue
mkADTTagAccess base = Contextualized (MemoryAccess (ADTTagAccess base))

mkADTUnionDataAccess :: GenValue -> LlvmValue -> GenValue
mkADTUnionDataAccess base = Contextualized (MemoryAccess (ADTUnionDataAccess base))

mkStructFieldAccess :: GenValue -> Int -> LlvmValue -> GenValue
mkStructFieldAccess base idx = Contextualized (MemoryAccess (StructFieldAccess base idx))

mkArrayElementAccess :: GenValue -> GenValue -> LlvmValue -> GenValue
mkArrayElementAccess arr idx = Contextualized (MemoryAccess (ArrayElementAccess arr idx))

mkArrayHeaderOffset :: GenValue -> LlvmValue -> GenValue
mkArrayHeaderOffset raw = Contextualized (MemoryAccess (ArrayHeaderOffset raw))

mkGlobalConstantAccess :: String -> LlvmType -> [Int] -> Bool -> LlvmValue -> GenValue
mkGlobalConstantAccess name ty idxs inb = Contextualized (MemoryAccess (GlobalConstantAccess name ty idxs inb))

mkDirectCall :: String -> [GenValue] -> LlvmValue -> GenValue
mkDirectCall fname args = Contextualized (FunctionCall (DirectCall fname args))

mkIndirectCall :: GenValue -> [GenValue] -> LlvmValue -> GenValue
mkIndirectCall fptr args = Contextualized (FunctionCall (IndirectCall fptr args))

mkStructValueLoad :: GenValue -> LlvmValue -> GenValue
mkStructValueLoad ptr = Contextualized (ValueLoad (StructValueLoad ptr))

mkArrayElementLoad :: GenValue -> GenValue -> LlvmValue -> GenValue
mkArrayElementLoad ptr idx = Contextualized (ValueLoad (ArrayElementLoad ptr idx))

mkVariableLoad :: GenValue -> Maybe String -> LlvmValue -> GenValue
mkVariableLoad ptr name = Contextualized (ValueLoad (VariableLoad ptr name))

mkFieldLoad :: GenValue -> Int -> LlvmValue -> GenValue
mkFieldLoad ptr idx = Contextualized (ValueLoad (FieldLoad ptr idx))

mkSliceConstruction :: GenValue -> Int -> LlvmValue -> GenValue
mkSliceConstruction ptr len = Contextualized (ArrayOperation (SliceConstruction ptr len))

mkSliceDeconstruction :: Maybe GenValue -> LlvmValue -> GenValue
mkSliceDeconstruction orig = Contextualized (ArrayOperation (SliceDeconstruction orig))

mkBinaryArith :: String -> GenValue -> GenValue -> LlvmValue -> GenValue
mkBinaryArith op lhs rhs = Contextualized (ArithmeticOp (BinaryArith op lhs rhs))

mkUnaryArith :: String -> GenValue -> LlvmValue -> GenValue
mkUnaryArith op oper = Contextualized (ArithmeticOp (UnaryArith op oper))

mkComparison :: String -> GenValue -> GenValue -> LlvmValue -> GenValue
mkComparison op lhs rhs = Contextualized (ComparisonOp (Comparison op lhs rhs))

mkBitcast :: GenValue -> LlvmType -> LlvmValue -> GenValue
mkBitcast src ty = Contextualized (TypeConversion (Bitcast src ty))

mkIntToPtr :: GenValue -> LlvmType -> LlvmValue -> GenValue
mkIntToPtr src ty = Contextualized (TypeConversion (IntToPtr src ty))

mkPtrToInt :: GenValue -> LlvmType -> LlvmValue -> GenValue
mkPtrToInt src ty = Contextualized (TypeConversion (PtrToInt src ty))

mkTruncate :: GenValue -> LlvmType -> LlvmValue -> GenValue
mkTruncate src ty = Contextualized (TypeConversion (Truncate src ty))

mkExtend :: GenValue -> LlvmType -> Bool -> LlvmValue -> GenValue
mkExtend src ty signed = Contextualized (TypeConversion (Extend src ty signed))

mkInsertValue :: Maybe GenValue -> GenValue -> Int -> LlvmValue -> GenValue
mkInsertValue target inserted idx = Contextualized (StructOperation (InsertValue target inserted idx))

mkExtractValue :: GenValue -> Int -> LlvmValue -> GenValue
mkExtractValue src idx = Contextualized (StructOperation (ExtractValue src idx))
