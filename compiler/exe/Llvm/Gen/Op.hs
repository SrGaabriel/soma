{-# LANGUAGE FlexibleContexts #-}

module Llvm.Gen.Op (
    compileOp,
) where

import Alloy.Ir
import Alloy.Naming (makeDictStructTypeName, qualifyWithModule)
import Control.Monad (foldM, foldM_)
import Control.Monad.Reader (asks)
import Control.Monad.Writer.Class (MonadWriter (tell))
import qualified Data.Map as Map
import Llvm.Gen.Core
import Llvm.Gen.Intrinsics (compileIntrinsic, isIntrinsic)
import Llvm.Gen.Operands (compileOperand)
import Llvm.Gen.TypeConversion (convertType)
import Llvm.Instructions
import Llvm.Types (LlvmType (..), deref)
import qualified Llvm.Types as LT
import Llvm.Values (LlvmValue (..), getValueType)
import Utils.Lists (hardHead)

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
    case callable of
        Direct fnName | isIntrinsic fnName -> do
            compileIntrinsic fnName aArgs opType
        _ -> do
            modName <- asks moduleName
            args <- mapM compileOperand aArgs
            fn <- case callable of
                Direct fnName -> pure $ LlvmGlobal opType ("\"" <> qualifyWithModule modName fnName <> "\"")
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
compileOp (OpMakeArray xs) _resultTy = do
    compiledXs <- mapM compileOperand xs
    let elemTy = if null compiledXs then LlvmI32 else getValueType (hardHead compiledXs)
    let arraySize = length xs
    -- todo: use resultTy instead
    let arrayTy = LlvmArray arraySize elemTy

    arrayPtr <- saveTmp (LlvmAlloca arrayTy Nothing) (LlvmPointer arrayTy)

    mapM_ (storeElem arrayPtr elemTy) (zip [0 ..] compiledXs)
    pure arrayPtr
  where
    storeElem :: LlvmValue -> LlvmType -> (Int, LlvmValue) -> IrGen ()
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
compileOp (OpGetDict className ty) _resultTy = do
    dMap <- asks dictMap
    modName <- asks moduleName
    case Map.lookup (className, ty) dMap of
        Just dictGlobalName -> do
            let dictStructType = LT.LlvmNamed (makeDictStructTypeName modName className)
            pure $ LlvmGlobal (LT.LlvmPtr dictStructType) dictGlobalName
        Nothing -> error $ "Dictionary not found for class " ++ className ++ " and type " ++ show ty
compileOp (OpDictCall dict methodIndex _methodName args) resultTy = do
    dictVal <- compileOperand dict

    compiledArgs <- mapM compileOperand args
    let argTypes = map getValueType compiledArgs

    let dictPtrType = getValueType dictVal
    let dictType = case dictPtrType of
            LlvmPointer t -> t
            t -> error $ "Dictionary operand is not a pointer: " ++ show t ++ "\nFrom operand: " ++ show dict ++ "\nCompiled to: " ++ show dictVal

    let indexZero = LlvmLiteral LlvmI32 "0"
    let methodIndexVal = LlvmLiteral LlvmI32 (show methodIndex)

    let fnPtrType = LT.LlvmFunctionPtr resultTy argTypes
    methodFieldPtr <-
        saveTmp
            (LlvmGetElementPtr dictType dictVal [indexZero, methodIndexVal] False)
            (LT.LlvmPtr fnPtrType)

    fnPtr <- saveTmp (LlvmLoad methodFieldPtr) fnPtrType

    if resultTy == LlvmVoid
        then do
            tell [LlvmCallStmt fnPtr resultTy compiledArgs]
            pure $ LlvmUndef LlvmVoid
        else saveTmp (LlvmCall fnPtr resultTy compiledArgs) resultTy

-- Lazy duplication: create a SUP node that lazily clones when projections are used
-- soma_dup(label, value) -> SUP handle
compileOp (OpDup label value) resultTy = do
    llValue <- compileOperand value
    let valueTy = getValueType llValue
    -- Cast value to i8* (void*) for the generic dup function
    voidPtr <- case valueTy of
        LlvmPointer _ -> saveTmp (LlvmBitcast llValue (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
        _ -> do
            -- For non-pointer types, we need to box them first
            -- For now, just use inttoptr (the runtime will handle it)
            saveTmp (LlvmIntToPtr llValue (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
    let labelVal = LlvmLiteral LlvmI32 (show label)
    -- Call soma_dup(label, value) -> returns SUP handle (i8*)
    let dupFunc = LlvmGlobal (LlvmPointer LlvmI8) "\"soma_dup\""
    supHandle <- saveTmp (LlvmCall dupFunc (LlvmPointer LlvmI8) [labelVal, voidPtr]) (LlvmPointer LlvmI8)
    -- Cast to result type if needed
    if resultTy == LlvmPointer LlvmI8
        then pure supHandle
        else saveTmp (LlvmBitcast supHandle resultTy) resultTy

-- First projection from SUP handle: soma_proj0(handle) -> value
compileOp (OpDupProj0 handle) resultTy = do
    llHandle <- compileOperand handle
    let handleTy = getValueType llHandle
    -- Ensure handle is i8*
    voidHandle <- case handleTy of
        LlvmPointer LlvmI8 -> pure llHandle
        LlvmPointer _ -> saveTmp (LlvmBitcast llHandle (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
        _ -> saveTmp (LlvmIntToPtr llHandle (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
    -- Call soma_proj0(handle) -> value (i8*)
    let proj0Func = LlvmGlobal (LlvmPointer LlvmI8) "\"soma_proj0\""
    result <- saveTmp (LlvmCall proj0Func (LlvmPointer LlvmI8) [voidHandle]) (LlvmPointer LlvmI8)
    -- Cast to result type
    if resultTy == LlvmPointer LlvmI8
        then pure result
        else case resultTy of
            LlvmPointer _ -> saveTmp (LlvmBitcast result resultTy) resultTy
            _ -> saveTmp (LlvmPtrToInt result resultTy) resultTy

-- Second projection from SUP handle: soma_proj1(handle) -> value
compileOp (OpDupProj1 handle) resultTy = do
    llHandle <- compileOperand handle
    let handleTy = getValueType llHandle
    -- Ensure handle is i8*
    voidHandle <- case handleTy of
        LlvmPointer LlvmI8 -> pure llHandle
        LlvmPointer _ -> saveTmp (LlvmBitcast llHandle (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
        _ -> saveTmp (LlvmIntToPtr llHandle (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
    -- Call soma_proj1(handle) -> value (i8*)
    let proj1Func = LlvmGlobal (LlvmPointer LlvmI8) "\"soma_proj1\""
    result <- saveTmp (LlvmCall proj1Func (LlvmPointer LlvmI8) [voidHandle]) (LlvmPointer LlvmI8)
    -- Cast to result type
    if resultTy == LlvmPointer LlvmI8
        then pure result
        else case resultTy of
            LlvmPointer _ -> saveTmp (LlvmBitcast result resultTy) resultTy
            _ -> saveTmp (LlvmPtrToInt result resultTy) resultTy

-- Wrap a function pointer in a SomaClosure structure
-- This is used before duplicating function-typed values so the runtime
-- can detect closures (via NODE_CLOSURE tag) and clone them properly.
-- soma_alloc_closure(func_ptr, arity=0, env_size=0) -> closure
compileOp (OpWrapClosure funcOp) resultTy = do
    llFunc <- compileOperand funcOp
    let funcTy = getValueType llFunc
    -- Ensure we have a pointer to the function
    funcPtr <- case funcTy of
        LlvmPointer _ -> pure llFunc
        _ -> saveTmp (LlvmIntToPtr llFunc (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
    -- Cast to i8* for the generic alloc_closure function
    voidFuncPtr <- saveTmp (LlvmBitcast funcPtr (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
    -- Call soma_alloc_closure(func_ptr, arity=0, env_size=0)
    -- Arity 0 means it's a "thunk" or saturated closure wrapper
    -- Env size 0 means no captured variables
    let allocClosureFunc = LlvmGlobal (LlvmPointer LlvmI8) "\"soma_alloc_closure\""
        arityVal = LlvmLiteral LlvmI8 "0"
        envSizeVal = LlvmLiteral LlvmI16 "0"
    closure <- saveTmp (LlvmCall allocClosureFunc (LlvmPointer LlvmI8) [voidFuncPtr, arityVal, envSizeVal]) (LlvmPointer LlvmI8)
    -- Cast to result type if needed
    if resultTy == LlvmPointer LlvmI8
        then pure closure
        else saveTmp (LlvmBitcast closure resultTy) resultTy

-- Allocate a closure with captured environment
-- soma_alloc_closure(func_ptr, arity, env_size) -> closure
compileOp (OpAllocClosure funcOp arity envSize) resultTy = do
    llFunc <- compileOperand funcOp
    let funcTy = getValueType llFunc
    -- Ensure we have a pointer to the function
    funcPtr <- case funcTy of
        LlvmPointer _ -> pure llFunc
        _ -> saveTmp (LlvmIntToPtr llFunc (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
    -- Cast to i8* for the generic alloc_closure function
    voidFuncPtr <- saveTmp (LlvmBitcast funcPtr (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
    -- Call soma_alloc_closure(func_ptr, arity, env_size)
    let allocClosureFunc = LlvmGlobal (LlvmPointer LlvmI8) "\"soma_alloc_closure\""
        arityVal = LlvmLiteral LlvmI8 (show arity)
        envSizeVal = LlvmLiteral LlvmI16 (show envSize)
    closure <- saveTmp (LlvmCall allocClosureFunc (LlvmPointer LlvmI8) [voidFuncPtr, arityVal, envSizeVal]) (LlvmPointer LlvmI8)
    -- Cast to result type if needed
    if resultTy == LlvmPointer LlvmI8
        then pure closure
        else saveTmp (LlvmBitcast closure resultTy) resultTy

-- Get value from closure environment slot
-- soma_closure_get_env(closure, index) -> value
compileOp (OpClosureGetEnv closureOp idx) resultTy = do
    llClosure <- compileOperand closureOp
    -- Ensure closure is i8*
    voidClosure <- case getValueType llClosure of
        LlvmPointer LlvmI8 -> pure llClosure
        LlvmPointer _ -> saveTmp (LlvmBitcast llClosure (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
        _ -> saveTmp (LlvmIntToPtr llClosure (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
    -- Call soma_closure_get_env(closure, index) -> returns SomaValue (i64)
    let getEnvFunc = LlvmGlobal LlvmI64 "\"soma_closure_get_env\""
        idxVal = LlvmLiteral LlvmI16 (show idx)
    result <- saveTmp (LlvmCall getEnvFunc LlvmI64 [voidClosure, idxVal]) LlvmI64
    -- Cast SomaValue (i64) to result type
    case resultTy of
        LlvmPointer _ -> saveTmp (LlvmIntToPtr result resultTy) resultTy
        _ -> do
            -- Shift right by 3 to get the integer value from the tagged pointer
            let shiftAmount = LlvmLiteral LlvmI64 "3"
            shifted <- saveTmp (LlvmAShr LlvmI64 result shiftAmount) LlvmI64
            saveTmp (LlvmTrunc shifted resultTy) resultTy

-- OpClosureSetEnv should have been lowered to EffClosureSetEnv
compileOp (OpClosureSetEnv{}) _ =
    error "OpClosureSetEnv should have been lowered to EffClosureSetEnv"
-- Get function pointer from closure
compileOp (OpClosureGetFunc closureOp) resultTy = do
    llClosure <- compileOperand closureOp
    -- For now, we access the func_ptr field directly (offset 8 in closure header)
    -- The closure structure is: { i8 tag, i8 arity, i16 env_size, ptr func_ptr }
    voidClosure <- case getValueType llClosure of
        LlvmPointer LlvmI8 -> pure llClosure
        LlvmPointer _ -> saveTmp (LlvmBitcast llClosure (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
        _ -> saveTmp (LlvmIntToPtr llClosure (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
    -- GEP to func_ptr field (index 4 in the padded struct)
    let closureStructType = LlvmNamedType "SomaClosure"
    funcPtrPtr <- saveTmp (LlvmGetElementPtr closureStructType voidClosure [LlvmLiteral LlvmI32 "0", LlvmLiteral LlvmI32 "4"] True) (LlvmPointer (LlvmPointer LlvmI8))
    result <- saveTmp (LlvmLoad funcPtrPtr) (LlvmPointer LlvmI8)
    -- Cast to result type if needed
    if resultTy == LlvmPointer LlvmI8
        then pure result
        else saveTmp (LlvmBitcast result resultTy) resultTy

-- Session 13: Specialized closure duplication operations

-- OpDupClosure: Create a SUP node for closure duplication
-- This is semantically equivalent to OpDup but carries slot type info for
-- the specialized projections that follow.
-- For now, we implement it the same as OpDup (the specialization is in the projections)
compileOp (OpDupClosure label closureOp _slotInfo) resultTy = do
    llClosure <- compileOperand closureOp
    let closureTy = getValueType llClosure
    -- Cast closure to i8* (void*) for the generic dup function
    voidPtr <- case closureTy of
        LlvmPointer _ -> saveTmp (LlvmBitcast llClosure (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
        _ -> saveTmp (LlvmIntToPtr llClosure (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
    let labelVal = LlvmLiteral LlvmI32 (show label)
    -- Call soma_dup(label, closure) -> returns SUP handle (i8*)
    let dupFunc = LlvmGlobal (LlvmPointer LlvmI8) "\"soma_dup\""
    supHandle <- saveTmp (LlvmCall dupFunc (LlvmPointer LlvmI8) [labelVal, voidPtr]) (LlvmPointer LlvmI8)
    -- Cast to result type if needed
    if resultTy == LlvmPointer LlvmI8
        then pure supHandle
        else saveTmp (LlvmBitcast supHandle resultTy) resultTy

-- OpDupClosureProj0: First projection of closure SUP
-- Returns the original closure. This is the "happy path" - no cloning needed.
-- The slotInfo is carried for consistency but not used here since we return original.
compileOp (OpDupClosureProj0 handleOp _envSize _slotInfo) resultTy = do
    llHandle <- compileOperand handleOp
    let handleTy = getValueType llHandle
    -- Ensure handle is i8*
    voidHandle <- case handleTy of
        LlvmPointer LlvmI8 -> pure llHandle
        LlvmPointer _ -> saveTmp (LlvmBitcast llHandle (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
        _ -> saveTmp (LlvmIntToPtr llHandle (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
    -- Call soma_proj0(handle) -> value (i8*)
    let proj0Func = LlvmGlobal (LlvmPointer LlvmI8) "\"soma_proj0\""
    result <- saveTmp (LlvmCall proj0Func (LlvmPointer LlvmI8) [voidHandle]) (LlvmPointer LlvmI8)
    -- Cast to result type
    if resultTy == LlvmPointer LlvmI8
        then pure result
        else case resultTy of
            LlvmPointer _ -> saveTmp (LlvmBitcast result resultTy) resultTy
            _ -> saveTmp (LlvmPtrToInt result resultTy) resultTy

-- OpDupClosureProj1: Second projection of closure SUP with HVM-style SUP propagation
-- When both projections are accessed, we clone the closure and wrap closure-typed
-- env slots in SUPs (using fresh labels) for lazy nested cloning.
--
-- For now, we use the existing soma_proj1 which does full cloning.
-- TODO: In a future iteration, implement inline specialized cloning that:
-- 1. Allocates a new closure
-- 2. Copies header
-- 3. For each env slot:
--    - If isClosure: wrap in SUP with fresh label via soma_fresh_label + soma_dup
--    - If not: direct copy
compileOp (OpDupClosureProj1 handleOp envSize slotInfo) resultTy = do
    llHandle <- compileOperand handleOp
    let handleTy = getValueType llHandle
    -- Ensure handle is i8*
    voidHandle <- case handleTy of
        LlvmPointer LlvmI8 -> pure llHandle
        LlvmPointer _ -> saveTmp (LlvmBitcast llHandle (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
        _ -> saveTmp (LlvmIntToPtr llHandle (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)

    -- For now, use the standard soma_proj1 which does full cloning
    -- In the future, we'll generate inline specialized code here
    if null [s | s@(_, True) <- slotInfo]
        then do
            -- No closure slots - standard cloning is fine
            let proj1Func = LlvmGlobal (LlvmPointer LlvmI8) "\"soma_proj1\""
            result <- saveTmp (LlvmCall proj1Func (LlvmPointer LlvmI8) [voidHandle]) (LlvmPointer LlvmI8)
            castResult result resultTy
        else do
            -- Has closure slots - use specialized inline cloning with SUP propagation
            -- This is the HVM-style incremental cloning
            result <- compileSpecializedClosureClone voidHandle envSize slotInfo
            castResult result resultTy
  where
    castResult result ty
        | ty == LlvmPointer LlvmI8 = pure result
        | otherwise = case ty of
            LlvmPointer _ -> saveTmp (LlvmBitcast result ty) ty
            _ -> saveTmp (LlvmPtrToInt result ty) ty

    -- Helper: Generate inline specialized closure cloning with SUP propagation
    -- This implements the HVM DUP-LAM rule: nested closures become SUPs
    compileSpecializedClosureClone :: LlvmValue -> Int -> SlotInfo -> IrGen LlvmValue
    compileSpecializedClosureClone supHandleArg envSizeArg slotInfoArg = do
        -- Call soma_proj1 for the base cloning, then post-process closure slots
        let proj1Func = LlvmGlobal (LlvmPointer LlvmI8) "\"soma_proj1\""
        baseResult <- saveTmp (LlvmCall proj1Func (LlvmPointer LlvmI8) [supHandleArg]) (LlvmPointer LlvmI8)

        -- Wrap closure-typed slots in SUPs for lazy nested cloning
        let closureSlots = [idx | (idx, isClosure) <- slotInfoArg, isClosure, idx < envSizeArg]

        -- Process closure slots - wrap each in a SUP with fresh label
        foldM_ wrapSlotInSUP baseResult closureSlots

        pure baseResult

    wrapSlotInSUP :: LlvmValue -> Int -> IrGen LlvmValue
    wrapSlotInSUP closure slotIdx = do
        -- Calculate slot offset: 16 (header) + slotIdx * 8
        let offset = 16 + slotIdx * 8
        let offsetVal = LlvmLiteral LlvmI64 (show offset)
        slotPtr <- saveTmp (LlvmGetElementPtr LlvmI8 closure [offsetVal] False) (LlvmPointer LlvmI8)

        -- Load current value
        currentVal <- saveTmp (LlvmLoadTyped (LlvmPointer LlvmI8) slotPtr) (LlvmPointer LlvmI8)

        -- Generate fresh label
        let freshLabelFunc = LlvmGlobal LlvmI32 "\"soma_fresh_label\""
        freshLabel <- saveTmp (LlvmCall freshLabelFunc LlvmI32 []) LlvmI32

        -- Create SUP for the nested closure
        let dupFunc = LlvmGlobal (LlvmPointer LlvmI8) "\"soma_dup\""
        supForSlot <- saveTmp (LlvmCall dupFunc (LlvmPointer LlvmI8) [freshLabel, currentVal]) (LlvmPointer LlvmI8)

        -- Store SUP back into the slot
        tell [LlvmStore supForSlot slotPtr]

        pure closure

-- OpClosureGetEnvDirect: Direct env slot access for original closures
-- Single load, no SUP projection needed
compileOp (OpClosureGetEnvDirect closureOp idx) resultTy = do
    llClosure <- compileOperand closureOp
    voidClosure <- case getValueType llClosure of
        LlvmPointer LlvmI8 -> pure llClosure
        LlvmPointer _ -> saveTmp (LlvmBitcast llClosure (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
        _ -> saveTmp (LlvmIntToPtr llClosure (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
    -- Call soma_closure_get_env(closure, index) - same as OpClosureGetEnv
    let getEnvFunc = LlvmGlobal (LlvmPointer LlvmI8) "\"soma_closure_get_env\""
        idxVal = LlvmLiteral LlvmI16 (show idx)
    result <- saveTmp (LlvmCall getEnvFunc (LlvmPointer LlvmI8) [voidClosure, idxVal]) (LlvmPointer LlvmI8)
    -- Cast to result type if needed
    if resultTy == LlvmPointer LlvmI8
        then pure result
        else case resultTy of
            LlvmPointer _ -> saveTmp (LlvmBitcast result resultTy) resultTy
            _ -> saveTmp (LlvmPtrToInt result resultTy) resultTy

-- OpClosureGetEnvSUP: SUP env slot access for cloned closures
-- The slot contains a SUP handle. We load it and project through using proj1
-- (since the clone is the "second copy" of the original closure)
compileOp (OpClosureGetEnvSUP closureOp idx) resultTy = do
    llClosure <- compileOperand closureOp
    voidClosure <- case getValueType llClosure of
        LlvmPointer LlvmI8 -> pure llClosure
        LlvmPointer _ -> saveTmp (LlvmBitcast llClosure (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
        _ -> saveTmp (LlvmIntToPtr llClosure (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
    -- Load the SUP from the env slot
    let getEnvFunc = LlvmGlobal (LlvmPointer LlvmI8) "\"soma_closure_get_env\""
        idxVal = LlvmLiteral LlvmI16 (show idx)
    supHandle <- saveTmp (LlvmCall getEnvFunc (LlvmPointer LlvmI8) [voidClosure, idxVal]) (LlvmPointer LlvmI8)
    -- Project through the SUP using proj1 (clone is "second copy")
    let proj1Func = LlvmGlobal (LlvmPointer LlvmI8) "\"soma_proj1\""
    result <- saveTmp (LlvmCall proj1Func (LlvmPointer LlvmI8) [supHandle]) (LlvmPointer LlvmI8)
    -- Cast to result type if needed
    if resultTy == LlvmPointer LlvmI8
        then pure result
        else case resultTy of
            LlvmPointer _ -> saveTmp (LlvmBitcast result resultTy) resultTy
            _ -> saveTmp (LlvmPtrToInt result resultTy) resultTy

-- Session 19: Parallel projection operations
-- These call soma_par_proj0/1 which may spawn the other branch as a parallel task
-- when workers are hungry and the work estimate exceeds the threshold.

-- OpParProj0: Parallel-aware first projection
-- soma_par_proj0 takes (SomaValue, u32) -> SomaValue (i64)
compileOp (OpParProj0 handleOp workEstimate) resultTy = do
    llHandle <- compileOperand handleOp
    let handleTy = getValueType llHandle
    -- Convert handle to i64 (SomaValue)
    i64Handle <- case handleTy of
        LlvmI64 -> pure llHandle
        LlvmPointer _ -> saveTmp (LlvmPtrToInt llHandle LlvmI64) LlvmI64
        _ -> saveTmp (LlvmSExt llHandle LlvmI64) LlvmI64
    -- Call soma_par_proj0(handle, work_estimate)
    let parProj0Func = LlvmGlobal LlvmI64 "\"soma_par_proj0\""
        workVal = LlvmLiteral LlvmI32 (show workEstimate)
    result <- saveTmp (LlvmCall parProj0Func LlvmI64 [i64Handle, workVal]) LlvmI64
    -- Convert result back to expected type
    case resultTy of
        LlvmI64 -> pure result
        LlvmPointer _ -> saveTmp (LlvmIntToPtr result resultTy) resultTy
        _ -> saveTmp (LlvmTrunc result resultTy) resultTy

-- OpParProj1: Parallel-aware second projection
-- soma_par_proj1 takes (SomaValue, u32) -> SomaValue (i64)
compileOp (OpParProj1 handleOp workEstimate) resultTy = do
    llHandle <- compileOperand handleOp
    let handleTy = getValueType llHandle
    -- Convert handle to i64 (SomaValue)
    i64Handle <- case handleTy of
        LlvmI64 -> pure llHandle
        LlvmPointer _ -> saveTmp (LlvmPtrToInt llHandle LlvmI64) LlvmI64
        _ -> saveTmp (LlvmSExt llHandle LlvmI64) LlvmI64
    -- Call soma_par_proj1(handle, work_estimate)
    let parProj1Func = LlvmGlobal LlvmI64 "\"soma_par_proj1\""
        workVal = LlvmLiteral LlvmI32 (show workEstimate)
    result <- saveTmp (LlvmCall parProj1Func LlvmI64 [i64Handle, workVal]) LlvmI64
    -- Convert result back to expected type
    case resultTy of
        LlvmI64 -> pure result
        LlvmPointer _ -> saveTmp (LlvmIntToPtr result resultTy) resultTy
        _ -> saveTmp (LlvmTrunc result resultTy) resultTy

-- OpParClosureProj0: Parallel-aware first projection for closures
-- soma_par_proj0 takes (SomaValue, u32) -> SomaValue (i64)
compileOp (OpParClosureProj0 handleOp _envSize _slotInfo workEstimate) resultTy = do
    llHandle <- compileOperand handleOp
    let handleTy = getValueType llHandle
    -- Convert handle to i64 (SomaValue)
    i64Handle <- case handleTy of
        LlvmI64 -> pure llHandle
        LlvmPointer _ -> saveTmp (LlvmPtrToInt llHandle LlvmI64) LlvmI64
        _ -> saveTmp (LlvmSExt llHandle LlvmI64) LlvmI64
    -- Call soma_par_proj0(handle, work_estimate)
    let parProj0Func = LlvmGlobal LlvmI64 "\"soma_par_proj0\""
        workVal = LlvmLiteral LlvmI32 (show workEstimate)
    result <- saveTmp (LlvmCall parProj0Func LlvmI64 [i64Handle, workVal]) LlvmI64
    -- Convert result back to expected type
    case resultTy of
        LlvmI64 -> pure result
        LlvmPointer _ -> saveTmp (LlvmIntToPtr result resultTy) resultTy
        _ -> saveTmp (LlvmTrunc result resultTy) resultTy

-- OpParClosureProj1: Parallel-aware second projection for closures
-- Similar to OpDupClosureProj1 but uses parallel runtime functions
-- soma_par_proj1 takes (SomaValue, u32) -> SomaValue (i64)
compileOp (OpParClosureProj1 handleOp envSize slotInfo workEstimate) resultTy = do
    llHandle <- compileOperand handleOp
    let handleTy = getValueType llHandle
    -- Convert handle to i64 (SomaValue)
    i64Handle <- case handleTy of
        LlvmI64 -> pure llHandle
        LlvmPointer _ -> saveTmp (LlvmPtrToInt llHandle LlvmI64) LlvmI64
        _ -> saveTmp (LlvmSExt llHandle LlvmI64) LlvmI64

    -- For closures with closure-typed slots, use specialized cloning with SUP propagation
    -- For simple closures, use parallel proj1
    if null [s | s@(_, True) <- slotInfo]
        then do
            -- No closure slots - use parallel proj1
            let parProj1Func = LlvmGlobal LlvmI64 "\"soma_par_proj1\""
                workVal = LlvmLiteral LlvmI32 (show workEstimate)
            result <- saveTmp (LlvmCall parProj1Func LlvmI64 [i64Handle, workVal]) LlvmI64
            castParResult result resultTy
        else do
            -- Has closure slots - use specialized cloning then parallel processing
            result <- compileParallelClosureClone i64Handle envSize slotInfo workEstimate
            castParResult result resultTy
  where
    castParResult result ty = case ty of
        LlvmI64 -> pure result
        LlvmPointer _ -> saveTmp (LlvmIntToPtr result ty) ty
        _ -> saveTmp (LlvmTrunc result ty) ty

    -- Specialized closure cloning with parallel awareness
    compileParallelClosureClone :: LlvmValue -> Int -> SlotInfo -> Int -> IrGen LlvmValue
    compileParallelClosureClone i64HandleArg envSizeArg slotInfoArg _workEst = do
        -- Use parallel proj1 for the base cloning
        let parProj1Func = LlvmGlobal LlvmI64 "\"soma_par_proj1\""
            workVal = LlvmLiteral LlvmI32 (show workEstimate)
        baseResultI64 <- saveTmp (LlvmCall parProj1Func LlvmI64 [i64HandleArg, workVal]) LlvmI64
        -- Convert to ptr for slot manipulation
        baseResult <- saveTmp (LlvmIntToPtr baseResultI64 (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)

        -- Wrap closure-typed slots in SUPs for lazy nested cloning
        let closureSlots = [idx | (idx, isClosure) <- slotInfoArg, isClosure, idx < envSizeArg]
        foldM_ wrapParSlotInSUP baseResult closureSlots
        -- Convert back to i64
        saveTmp (LlvmPtrToInt baseResult LlvmI64) LlvmI64

    wrapParSlotInSUP :: LlvmValue -> Int -> IrGen LlvmValue
    wrapParSlotInSUP closure slotIdx = do
        let offset = 16 + slotIdx * 8
            offsetVal = LlvmLiteral LlvmI64 (show offset)
        slotPtr <- saveTmp (LlvmGetElementPtr LlvmI8 closure [offsetVal] False) (LlvmPointer LlvmI8)
        currentVal <- saveTmp (LlvmLoadTyped (LlvmPointer LlvmI8) slotPtr) (LlvmPointer LlvmI8)
        let freshLabelFunc = LlvmGlobal LlvmI32 "\"soma_fresh_label\""
        freshLabel <- saveTmp (LlvmCall freshLabelFunc LlvmI32 []) LlvmI32
        let dupFunc = LlvmGlobal (LlvmPointer LlvmI8) "\"soma_dup\""
        supForSlot <- saveTmp (LlvmCall dupFunc (LlvmPointer LlvmI8) [freshLabel, currentVal]) (LlvmPointer LlvmI8)
        tell [LlvmStore supForSlot slotPtr]
        pure closure

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
