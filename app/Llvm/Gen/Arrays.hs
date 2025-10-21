module Llvm.Gen.Arrays where

import Control.Monad.State (modify)
import Control.Monad.Writer (tell)
import Llvm.Dependencies (LlvmDependency (LlvmFunctionDependency))
import Llvm.Gen.Context
import Llvm.Gen.Core (IrGen, IrGenState (..), mkFnCall, saveInstruction)
import Llvm.Gen.Types (sliceType)
import Llvm.Instructions (LlvmInstruction (..), LlvmStatement (..))
import Llvm.Types (LlvmType (..), getLlvmTypeSize)
import Llvm.Values (LlvmValue (..), intLiteral, intLiteral)

createStackArray :: LlvmType -> Int -> IrGen LlvmValue
createStackArray elemType len = do
    let arrayType = LlvmArray len elemType
    saveInstruction (LlvmAlloca arrayType Nothing) (LlvmPointer LlvmI8)

createSlice :: GenValue -> Int -> IrGen GenValue
createSlice dataPtr len = do
    let lenValue = LlvmLiteral LlvmI32 (show len)

    reg1 <- saveInstruction (LlvmInsertValue sliceType LlvmUndef (gvw dataPtr) 0) sliceType
    mkSliceConstruction dataPtr len
        <$> saveInstruction (LlvmInsertValue sliceType reg1 lenValue 1) sliceType

extractSlicePtr :: GenValue -> IrGen GenValue
extractSlicePtr slice = do
    mkSliceDeconstruction (Just slice)
        <$> saveInstruction (LlvmExtractValue sliceType (gvw slice) 0) (LlvmPointer LlvmI8)

extractSliceLen :: GenValue -> IrGen GenValue
extractSliceLen slice = do
    mkSliceDeconstruction (Just slice)
        <$> saveInstruction (LlvmExtractValue sliceType (gvw slice) 1) LlvmI32

heapArrayHeaderSize :: Int
heapArrayHeaderSize = 16

createTypedRefCountedHeapArray :: LlvmType -> Int -> IrGen GenValue
createTypedRefCountedHeapArray elemType len = do
    let bytesPerElem = getLlvmTypeSize elemType
    let totalBytes = heapArrayHeaderSize + len * bytesPerElem
    createRefCountedHeapArray elemType (cIntLiteral totalBytes) (cIntLiteral len)

createTypedDynamicSizedRefCountedHeapArray :: LlvmType -> GenValue -> IrGen GenValue
createTypedDynamicSizedRefCountedHeapArray elemType len = do
    let bytesPerElem = cIntLiteral $ getLlvmTypeSize elemType
    bytesWithoutHeader <-
        mkBinaryArith "mul" len bytesPerElem
            <$> saveInstruction
                (LlvmMul LlvmI32 (gvw len) (gvw bytesPerElem))
                LlvmI32
    totalBytes <-
        mkBinaryArith "add" bytesWithoutHeader (cIntLiteral heapArrayHeaderSize)
            <$> saveInstruction
                (LlvmAdd LlvmI32 (gvw bytesWithoutHeader) (intLiteral heapArrayHeaderSize))
                LlvmI32
    createRefCountedHeapArray elemType totalBytes len

createRefCountedHeapArray :: LlvmType -> GenValue -> GenValue -> IrGen GenValue
createRefCountedHeapArray elemType initialSize len = do
    rawPtr <- saveInstruction (mkFnCall "malloc" [initialSize] (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
    let mallocDependency = LlvmFunctionDependency "malloc" (LlvmPointer LlvmI8) [LlvmI32]
    modify $ \s -> s{irDependencies = mallocDependency : irDependencies s}

    let cRawPtr = mkHeapAlloc (LlvmPointer LlvmI8) initialSize rawPtr
    castedRawPtr <- saveInstruction (LlvmBitcast rawPtr (LlvmPointer LlvmI32)) (LlvmPointer LlvmI32)
    tell [LlvmStore LlvmI32 (intLiteral 1) castedRawPtr]

    lenOffsetPtr <- saveInstruction (LlvmGetElementPtr LlvmI32 castedRawPtr [intLiteral 1] True) (LlvmPointer LlvmI32)
    tell [LlvmStore LlvmI32 (gvw len) lenOffsetPtr]

    mkArrayHeaderOffset cRawPtr elemType
        <$> saveInstruction (LlvmGetElementPtr LlvmI8 rawPtr [intLiteral heapArrayHeaderSize] True) (LlvmPointer LlvmI8)

storeArrayElement :: GenValue -> GenValue -> GenValue -> LlvmType -> IrGen ()
storeArrayElement arrayPtr index value elemType = do
    elemPtr <-
        saveInstruction
            (LlvmGetElementPtr elemType (gvw arrayPtr) [gvw index] True)
            (LlvmPointer LlvmI8)
    tell [LlvmStore elemType (gvw value) elemPtr]

loadArrayElement :: GenValue -> GenValue -> LlvmType -> IrGen GenValue
loadArrayElement arrayPtr index elemType = do
    ptrInStr <- extractSlicePtr arrayPtr
    elemPtr <-
        mkArrayElementAccess arrayPtr index
            <$> saveInstruction
                (LlvmGetElementPtr elemType (gvw ptrInStr) [gvw index] True)
                (LlvmPointer elemType)
    mkArrayElementLoad elemPtr index
        <$> saveInstruction (LlvmLoad (gvw elemPtr)) elemType

getStackArrayDataPtr :: LlvmValue -> LlvmType -> IrGen LlvmValue
getStackArrayDataPtr stackPtr arrayType = do
    saveInstruction
        (LlvmGetElementPtr arrayType stackPtr [intLiteral 0, intLiteral 0] True)
        (LlvmPointer LlvmI8)