{-# LANGUAGE FlexibleContexts #-}

module Llvm.Gen.Op (
    compileOp,
) where

import Alloy.Ir
import Control.Monad (foldM)
import Control.Monad.Writer.Class (tell)
import Llvm.Gen.Core
import Llvm.Gen.Operands (compileOperand)
import Llvm.Gen.TypeConversion (convertType)
import Llvm.Instructions
import Llvm.Types (LlvmType (..), deref)
import Llvm.Values (LlvmValue (..), getValueType)

compileOp :: AOp -> LlvmType -> IrGen LlvmValue
compileOp (OpLoad rOperand) resultTy = do
    operand <- compileOperand rOperand
    saveTmp (LlvmLoad operand) resultTy
compileOp (OpAllocStack ty) resultTy = do
    let llvmTy = convertType ty
    saveTmp (LlvmAlloca llvmTy Nothing) resultTy
compileOp (OpBin k a b) resultTy = do
    lhs <- compileOperand a
    rhs <- compileOperand b
    let ty = getValueType lhs
    let instr = case k of
            IAdd -> LlvmAdd ty lhs rhs
            ISub -> LlvmSub ty lhs rhs
            IMul -> LlvmMul ty lhs rhs
            other -> error $ "Unsupported binary op in LLVM codegen: " ++ show other
    saveTmp instr resultTy
compileOp (OpUnary k a) resultTy = do
    v <- compileOperand a
    let ty = getValueType v
    let instr = case k of
            Neg -> let zero = LlvmLiteral ty "0" in LlvmSub ty zero v
            Not ->
                if ty == LlvmI1
                    then LlvmICmp ty "eq" v (LlvmLiteral LlvmI1 "0")
                    else error "Bitwise NOT for non-boolean not supported in LLVM codegen yet"
    saveTmp instr resultTy
compileOp (OpCmp c a b) resultTy = do
    lhs <- compileOperand a
    rhs <- compileOperand b
    let ty = getValueType lhs
    saveTmp (LlvmICmp ty (cmpOpToLlvm c) lhs rhs) resultTy
compileOp (OpIndex base idx) resultTy = do
    b <- compileOperand base
    i <- compileOperand idx
    let elemTy = deref (getValueType b)
    saveTmp (LlvmGetElementPtr elemTy b [i] True) resultTy
compileOp (OpProject agg ix) resultTy = do
    av <- compileOperand agg
    let aggTy = getValueType av
    case aggTy of
        LlvmAnonymous _ -> do
            if ix == 0
                then do
                    payloadVal <- saveTmp (LlvmExtractValue aggTy av 1) LlvmI64
                    bitcastFromPayload payloadVal resultTy
                else
                    error $ "Multi-field ADT projection not yet supported: index " ++ show ix
        _ ->
            saveTmp (LlvmExtractValue aggTy av ix) resultTy
  where
    bitcastFromPayload :: LlvmValue -> LlvmType -> IrGen LlvmValue
    bitcastFromPayload val targetTy
        | targetTy == LlvmI64 = pure val
        | targetTy == LlvmI32 = saveTmp (LlvmTrunc val LlvmI32) LlvmI32
        | targetTy == LlvmI8 = saveTmp (LlvmTrunc val LlvmI8) LlvmI8
        | targetTy == LlvmI1 = saveTmp (LlvmTrunc val LlvmI1) LlvmI1
        | LlvmPointer _ <- targetTy = saveTmp (LlvmIntToPtr val targetTy) targetTy
        | otherwise = error $ "Unsupported type for payload extraction: " ++ show targetTy
compileOp (OpCall callable aArgs) opType = do
    args <- mapM compileOperand aArgs
    fn <- case callable of
        Direct fnName -> pure $ LlvmGlobal opType fnName
        Indirect operand -> compileOperand operand
    if opType == LlvmVoid
        then do
            tell [LlvmCallStmt fn opType args]
            pure $ LlvmUndef LlvmVoid
        else saveTmp (LlvmCall fn opType args) opType
compileOp (OpConstruct _cName cTag cFields) resultTy = do
    fieldVals <- mapM compileOperand cFields
    let undefVal = LlvmUndef resultTy

    let tagLiteral = LlvmLiteral LlvmI8 (show cTag)
    withTag <- saveTmp (LlvmInsertValue resultTy undefVal tagLiteral 0) resultTy

    case fieldVals of
        [] -> pure withTag
        [fieldVal] -> do
            let fieldTy = getValueType fieldVal
            payloadVal <- bitcastToPayload fieldVal fieldTy
            saveTmp (LlvmInsertValue resultTy withTag payloadVal 1) resultTy
        _ -> error "Multi-field constructors not yet supported in universal payload representation"
  where
    bitcastToPayload :: LlvmValue -> LlvmType -> IrGen LlvmValue
    bitcastToPayload val valTy
        | valTy == LlvmI64 = pure val -- Already i64
        | valTy == LlvmI32 = saveTmp (LlvmZExt val LlvmI64) LlvmI64
        | valTy == LlvmI8 = saveTmp (LlvmZExt val LlvmI64) LlvmI64
        | valTy == LlvmI1 = saveTmp (LlvmZExt val LlvmI64) LlvmI64
        | LlvmPointer _ <- valTy = saveTmp (LlvmPtrToInt val LlvmI64) LlvmI64
        | otherwise = error $ "Unsupported type for payload conversion: " ++ show valTy
compileOp (OpTagOf agg) resultTy = do
    av <- compileOperand agg
    let aggTy = getValueType av
    saveTmp (LlvmExtractValue aggTy av 0) resultTy
compileOp (OpMakeArray xs) resultTy = do
    compiledXs <- mapM compileOperand xs
    let elemTy = if null compiledXs then LlvmI32 else getValueType (head compiledXs)
    let arraySize = length xs
    let arrayTy = LlvmArray arraySize elemTy

    arrayPtr <- saveTmp (LlvmAlloca arrayTy Nothing) (LlvmPointer arrayTy)

    mapM_ (storeElem arrayPtr elemTy) (zip [0 ..] compiledXs)
    pure arrayPtr
  where
    storeElem arrayPtr elemTy (idx, val) = do
        let idxVal = LlvmLiteral LlvmI32 (show idx)
        elemPtr <- saveTmp (LlvmGetElementPtr elemTy arrayPtr [idxVal] True) (LlvmPointer elemTy)
        tell [LlvmStore val elemPtr]
compileOp (OpMakeTuple xs) resultTy = do
    compiledXs <- mapM compileOperand xs

    let undefVal = LlvmUndef resultTy
    foldM insertElem undefVal (zip [0 ..] compiledXs)
  where
    insertElem :: LlvmValue -> (Int, LlvmValue) -> IrGen LlvmValue
    insertElem tupleVal (idx, elemVal) = do
        saveTmp (LlvmInsertValue resultTy tupleVal elemVal idx) resultTy
compileOp (OpAllocHeap ty) resultTy = do
    let llvmTy = convertType ty
    saveTmp (LlvmAlloca llvmTy Nothing) resultTy
compileOp op _ = error $ "Unimplemented operation in LLVM codegen: " ++ show op

cmpOpToLlvm :: ACmpOp -> String
cmpOpToLlvm CEq = "eq"
cmpOpToLlvm CNe = "ne"
cmpOpToLlvm CUlt = "ult"
cmpOpToLlvm CUle = "ule"
cmpOpToLlvm CUgt = "ugt"
cmpOpToLlvm CUge = "uge"
cmpOpToLlvm CSlt = "slt"
cmpOpToLlvm CSle = "sle"
cmpOpToLlvm CSgt = "sgt"
cmpOpToLlvm CSge = "sge"
