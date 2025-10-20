module Llvm.Gen.Arrays where

import Control.Monad.State (modify)
import Control.Monad.Writer (tell)
import Llvm.Gen.Core (IrGen, IrGenState (..), saveInstruction)
import Llvm.Gen.Types (sliceType)
import Llvm.Instructions (LlvmInstruction (..), LlvmStatement (..))
import Llvm.Types (LlvmType (..), getLlvmTypeSize)
import Llvm.Values (LlvmValue (..), intLiteral, longLiteral)
import Llvm.Dependencies (LlvmDependency (LlvmFunctionDependency))

createStackArray :: LlvmType -> Int -> IrGen LlvmValue
createStackArray elemType len = do
    let arrayType = LlvmArray len elemType
    saveInstruction (LlvmAlloca arrayType Nothing) LlvmPtr

createSlice :: LlvmValue -> Int -> IrGen LlvmValue
createSlice dataPtr len = do
    let lenValue = LlvmLiteral LlvmI64 (show len)

    reg1 <- saveInstruction (LlvmInsertValue sliceType LlvmUndef dataPtr 0) sliceType
    saveInstruction (LlvmInsertValue sliceType reg1 lenValue 1) sliceType

extractSlicePtr :: LlvmValue -> IrGen LlvmValue
extractSlicePtr slice = do
    saveInstruction (LlvmExtractValue sliceType slice 0) LlvmPtr

extractSliceLen :: LlvmValue -> IrGen LlvmValue
extractSliceLen slice = do
    saveInstruction (LlvmExtractValue sliceType slice 1) LlvmI64

createRefCountedHeapArray :: LlvmType -> Int -> IrGen LlvmValue
createRefCountedHeapArray elemType len = do
    let bytesPerElem = getLlvmTypeSize elemType
    let headerSize = 16
    let totalBytes = headerSize + len * bytesPerElem

    rawPtr <- saveInstruction (LlvmCall (LlvmGlobal LlvmFn "malloc") LlvmPtr [longLiteral totalBytes]) LlvmPtr
    let mallocDependency = LlvmFunctionDependency "malloc" (LlvmPointer LlvmI8) [LlvmI64]
    modify $ \s -> s{irDependencies = mallocDependency : irDependencies s}

    castedRawPtr <- saveInstruction (LlvmBitcast rawPtr (LlvmPointer LlvmI64)) (LlvmPointer LlvmI64)
    tell [LlvmStore LlvmI64 (longLiteral 1) castedRawPtr]

    lenOffsetPtr <- saveInstruction (LlvmGetElementPtr LlvmI64 castedRawPtr [intLiteral 1] True) (LlvmPointer LlvmI64)
    tell [LlvmStore LlvmI64 (longLiteral (fromIntegral len)) lenOffsetPtr]

    saveInstruction (LlvmGetElementPtr LlvmI8 rawPtr [longLiteral headerSize] True) LlvmPtr

storeArrayElement :: LlvmValue -> LlvmValue -> LlvmValue -> LlvmType -> IrGen ()
storeArrayElement arrayPtr index value elemType = do
    elemPtr <-
        saveInstruction
            (LlvmGetElementPtr elemType arrayPtr [index] True)
            LlvmPtr
    tell [LlvmStore elemType value elemPtr]

loadArrayElement :: LlvmValue -> LlvmValue -> LlvmType -> IrGen LlvmValue
loadArrayElement arrayPtr index elemType = do
    elemPtr <-
        saveInstruction
            (LlvmGetElementPtr elemType arrayPtr [index] True)
            LlvmPtr
    saveInstruction (LlvmLoad elemPtr) elemType

getStackArrayDataPtr :: LlvmValue -> LlvmType -> IrGen LlvmValue
getStackArrayDataPtr stackPtr arrayType = do
    saveInstruction
        (LlvmGetElementPtr arrayType stackPtr [longLiteral 0, longLiteral 0] True)
        LlvmPtr
