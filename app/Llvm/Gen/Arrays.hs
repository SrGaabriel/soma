module Llvm.Gen.Arrays where

import Control.Monad.State (modify)
import Control.Monad.Writer (tell)
import Llvm.Dependencies (LlvmDependency (LlvmFunctionDependency))
import Llvm.Gen.Context
import Llvm.Gen.Core (IrGen, IrGenState (..), saveInstruction, mkFnCall)
import Llvm.Gen.Types (sliceType)
import Llvm.Instructions (LlvmInstruction (..), LlvmStatement (..))
import Llvm.Types (LlvmType (..), getLlvmTypeSize)
import Llvm.Values (LlvmValue (..), intLiteral, longLiteral)

createStackArray :: LlvmType -> Int -> IrGen LlvmValue
createStackArray elemType len = do
    let arrayType = LlvmArray len elemType
    saveInstruction (LlvmAlloca arrayType Nothing) LlvmPtr

createSlice :: GenValue -> Int -> IrGen GenValue
createSlice dataPtr len = do
    let lenValue = LlvmLiteral LlvmI64 (show len)

    reg1 <- saveInstruction (LlvmInsertValue sliceType LlvmUndef (gvw dataPtr) 0) sliceType
    mkSliceConstruction dataPtr len
        <$> saveInstruction (LlvmInsertValue sliceType reg1 lenValue 1) sliceType

extractSlicePtr :: LlvmValue -> IrGen LlvmValue
extractSlicePtr slice = do
    saveInstruction (LlvmExtractValue sliceType slice 0) LlvmPtr

extractSliceLen :: LlvmValue -> IrGen LlvmValue
extractSliceLen slice = do
    saveInstruction (LlvmExtractValue sliceType slice 1) LlvmI64

heapArrayHeaderSize :: Int
heapArrayHeaderSize = 16

createTypedRefCountedHeapArray :: LlvmType -> Int -> IrGen GenValue
createTypedRefCountedHeapArray elemType len = do
    let bytesPerElem = getLlvmTypeSize elemType
    let totalBytes = heapArrayHeaderSize + len * bytesPerElem
    createRefCountedHeapArray totalBytes len

createRefCountedHeapArray :: Int -> Int -> IrGen GenValue
createRefCountedHeapArray initialSize len = do
    rawPtr <- saveInstruction (mkFnCall "malloc" [cLongLiteral initialSize] LlvmPtr) LlvmPtr
    let mallocDependency = LlvmFunctionDependency "malloc" (LlvmPointer LlvmI8) [LlvmI64]
    modify $ \s -> s{irDependencies = mallocDependency : irDependencies s}

    let cRawPtr = mkHeapAlloc LlvmPtr initialSize rawPtr
    castedRawPtr <- saveInstruction (LlvmBitcast rawPtr (LlvmPointer LlvmI64)) (LlvmPointer LlvmI64)
    tell [LlvmStore LlvmI64 (longLiteral 1) castedRawPtr]

    lenOffsetPtr <- saveInstruction (LlvmGetElementPtr LlvmI64 castedRawPtr [intLiteral 1] True) (LlvmPointer LlvmI64)
    tell [LlvmStore LlvmI64 (longLiteral (fromIntegral len)) lenOffsetPtr]

    mkArrayHeaderOffset cRawPtr
        <$> saveInstruction (LlvmGetElementPtr LlvmI8 rawPtr [longLiteral heapArrayHeaderSize] True) LlvmPtr

storeArrayElement :: GenValue -> GenValue -> GenValue -> LlvmType -> IrGen ()
storeArrayElement arrayPtr index value elemType = do
    elemPtr <-
        saveInstruction
            (LlvmGetElementPtr elemType (gvw arrayPtr) [gvw index] True)
            LlvmPtr
    tell [LlvmStore elemType (gvw value) elemPtr]

loadArrayElement :: GenValue -> GenValue -> LlvmType -> IrGen GenValue
loadArrayElement arrayPtr index elemType = do
    elemPtr <-
        mkArrayElementAccess arrayPtr index
            <$> saveInstruction
                (LlvmGetElementPtr elemType (gvw arrayPtr) [gvw index] True)
                LlvmPtr
    mkArrayElementLoad elemPtr index
        <$> saveInstruction (LlvmLoad (gvw elemPtr)) elemType

getStackArrayDataPtr :: LlvmValue -> LlvmType -> IrGen LlvmValue
getStackArrayDataPtr stackPtr arrayType = do
    saveInstruction
        (LlvmGetElementPtr arrayType stackPtr [longLiteral 0, longLiteral 0] True)
        LlvmPtr
