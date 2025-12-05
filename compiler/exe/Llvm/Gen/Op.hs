{-# LANGUAGE FlexibleContexts #-}

module Llvm.Gen.Op (
    compileOp,
) where

import Alloy.Ir
import Alloy.Naming (makeDictStructTypeName, qualifyWithModule)
import Control.Monad (foldM, foldM_, forM, forM_)
import Control.Monad.Reader (asks)
import Control.Monad.State (modify)
import Control.Monad.Writer.Class (MonadWriter (tell))
import qualified Data.Map as Map
import Llvm.Gen.CRuntime (
    cruntimeGInet,
    cruntimeGInetTm,
    cruntimeInetApp,
    cruntimeInetClosure,
    cruntimeInetClosureGetEnv,
    cruntimeInetCon,
    cruntimeInetDupEager,
    cruntimeInetFree,
    cruntimeInetGet,
    cruntimeInetGetNumExt,
    cruntimeInetInitGlobals,
    cruntimeInetLam,
    cruntimeInetNumExt,
    cruntimeInetOpr,
    cruntimeInetReduce,
    cruntimeInetRef,
    cruntimeInetRegisterFunc,
    cruntimeInetSup,
    cruntimeSomaAllocClosure,
    cruntimeSomaClosureGetEnv,
    cruntimeSomaClosureType,
    cruntimeSomaDup,
    cruntimeSomaForkDirect,
    cruntimeSomaForkMulti,
    cruntimeSomaFreshLabel,
    cruntimeSomaJoin,
    cruntimeSomaPanic,
    cruntimeSomaParEnabledExport,
    cruntimeSomaParProj0,
    cruntimeSomaParProj1,
    cruntimeSomaPoolAllocClosure,
    cruntimeSomaProj0,
    cruntimeSomaProj1,
 )
import Llvm.Gen.Core
import Llvm.Gen.Externals (mallocDependency, memcpyDependency, useDep, useType)
import Llvm.Gen.Intrinsics (compileIntrinsic, isIntrinsic)
import Llvm.Gen.Operands (compileOperand)
import Llvm.Gen.Templates (newStrTemplate)
import Llvm.Gen.TypeConversion (convertType)
import Llvm.Instructions
import Llvm.Modules (LlvmBlock (..), LlvmFunction (..))
import Llvm.Types (LlvmFnAttr (..), LlvmType (..), deref)
import qualified Llvm.Types as LT
import Llvm.Values (LlvmValue (..), getValueType)
import Utils.Lists (hardHead)

-- ============================================================================
-- Helper functions for INET graph operations
-- ============================================================================

{- | Get the net and tm pointers for INET operations.
Inside graph functions (with net, tm params), use the parameters.
Otherwise, load from globals.
-}
getNetAndTm :: IrGen (LlvmValue, LlvmValue)
getNetAndTm = do
    inGraphFn <- isInGraphFunction
    if inGraphFn
        then do
            -- Use function parameters directly
            let net = LlvmRegister (LlvmPointer LlvmI8) "net"
                tm = LlvmRegister (LlvmPointer LlvmI8) "tm"
            pure (net, tm)
        else do
            -- Load from globals
            globalNetPtr <- useDep cruntimeGInet
            net <- saveTmp (LlvmLoad globalNetPtr) (LlvmPointer LlvmI8)
            globalTmPtr <- useDep cruntimeGInetTm
            tm <- saveTmp (LlvmLoad globalTmPtr) (LlvmPointer LlvmI8)
            pure (net, tm)

-- | Get just the net pointer (for inet_reduce which only needs net)
getNet :: IrGen LlvmValue
getNet = do
    inGraphFn <- isInGraphFunction
    if inGraphFn
        then pure $ LlvmRegister (LlvmPointer LlvmI8) "net"
        else do
            globalNetPtr <- useDep cruntimeGInet
            saveTmp (LlvmLoad globalNetPtr) (LlvmPointer LlvmI8)

-- ============================================================================
-- Op compilation
-- ============================================================================

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
            IDiv -> LlvmSDiv ty lhs rhs
            IMod -> LlvmSRem ty lhs rhs
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
compileOp (OpSelect cond trueVal falseVal) resultTy = do
    c <- compileOperand cond
    t <- compileOperand trueVal
    f <- compileOperand falseVal
    let ty = getValueType t
    saveTmp (LlvmSelect c t f ty) resultTy
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
            -- Extract the payload (always at index 1 in {i8, i64} struct)
            payloadVal <- saveTmp (LlvmExtractValue aggTy av 1) LlvmI64
            if ix == 0
                then
                    -- Single-field: payload IS the value
                    bitcastFromPayload payloadVal resultTy
                else do
                    -- Multi-field: payload is a pointer to array of i64
                    -- Convert i64 payload back to pointer
                    payloadPtr <- saveTmp (LlvmIntToPtr payloadVal (LlvmPointer LlvmI64)) (LlvmPointer LlvmI64)
                    -- GEP to the field at index ix
                    fieldPtr <- saveTmp (LlvmGetElementPtr LlvmI64 payloadPtr [LlvmLiteral LlvmI64 (show ix)] True) (LlvmPointer LlvmI64)
                    -- Load the field value
                    fieldVal <- saveTmp (LlvmLoadTyped LlvmI64 fieldPtr) LlvmI64
                    bitcastFromPayload fieldVal resultTy
        -- For primitive types (i32, i64, etc.), the value itself is the "payload"
        -- This happens in pattern matching on Int literals where a variable binding
        -- needs to capture the scrutinee value
        LlvmI32 -> castPrimitive av aggTy resultTy
        LlvmI64 -> castPrimitive av aggTy resultTy
        LlvmI8 -> castPrimitive av aggTy resultTy
        LlvmI1 -> castPrimitive av aggTy resultTy
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
    -- Cast a primitive value to the result type (for pattern match variable bindings)
    castPrimitive :: LlvmValue -> LlvmType -> LlvmType -> IrGen LlvmValue
    castPrimitive val srcTy tgtTy
        | srcTy == tgtTy = saveTmp (LlvmIdentityCast val) tgtTy
        | otherwise = case (srcTy, tgtTy) of
            (LlvmI32, LlvmI64) -> saveTmp (LlvmSExt val tgtTy) tgtTy
            (LlvmI64, LlvmI32) -> saveTmp (LlvmTrunc val tgtTy) tgtTy
            (LlvmI8, LlvmI32) -> saveTmp (LlvmSExt val tgtTy) tgtTy
            (LlvmI8, LlvmI64) -> saveTmp (LlvmSExt val tgtTy) tgtTy
            (LlvmI1, LlvmI32) -> saveTmp (LlvmZExt val tgtTy) tgtTy
            (LlvmI1, LlvmI64) -> saveTmp (LlvmZExt val tgtTy) tgtTy
            _ -> saveTmp (LlvmIdentityCast val) tgtTy
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
            isTail <- isTailCallContext
            if opType == LlvmVoid
                then do
                    tell [LlvmCallStmt fn opType args]
                    pure $ LlvmUndef LlvmVoid
                else
                    if isTail
                        then saveTmp (LlvmTailCall fn opType args) opType
                        else saveTmp (LlvmCall fn opType args) opType
compileOp (OpConstruct _cName cTag cFields) resultTy = do
    fieldVals <- mapM compileOperand cFields

    -- Special case: Array literals use tag -2 and result in pointer types
    case resultTy of
        LlvmPointer elemTy | cTag == -2 -> do
            let arraySize = length fieldVals
            let arrayTy = LlvmArray arraySize elemTy
            mallocFn <- useDep mallocDependency
            let allocSize = LlvmLiteral LlvmI64 (show (arraySize * 8)) -- 8 bytes per element
            rawPtr <- saveTmp (LlvmCall mallocFn (LlvmPointer LlvmI8) [allocSize]) (LlvmPointer LlvmI8)
            arrayPtr <- saveTmp (LlvmBitcast rawPtr (LlvmPointer arrayTy)) (LlvmPointer arrayTy)
            forM_ (zip [0 ..] fieldVals) $ \(idx, val) -> do
                let idxVal = LlvmLiteral LlvmI64 (show (idx :: Int))
                elemPtr <- saveTmp (LlvmGetElementPtr elemTy arrayPtr [idxVal] True) (LlvmPointer elemTy)
                tell [LlvmStore val elemPtr]
            pure arrayPtr
        _ -> do
            let undefVal = LlvmUndef resultTy
            let tagLiteral = LlvmLiteral LlvmI8 (show cTag)
            withTag <- saveTmp (LlvmInsertValue resultTy undefVal tagLiteral 0) resultTy

            case fieldVals of
                [] -> pure withTag
                [fieldVal] -> do
                    let fieldTy = getValueType fieldVal
                    payloadVal <- bitcastToPayload fieldVal fieldTy
                    saveTmp (LlvmInsertValue resultTy withTag payloadVal 1) resultTy
                _ -> do
                    let numFields = length fieldVals
                    let allocSize = LlvmLiteral LlvmI64 (show (numFields * 8)) -- 8 bytes per i64
                    mallocFn <- useDep mallocDependency
                    rawPtr <- saveTmp (LlvmCall mallocFn (LlvmPointer LlvmI8) [allocSize]) (LlvmPointer LlvmI8)
                    arrPtr <- saveTmp (LlvmBitcast rawPtr (LlvmPointer LlvmI64)) (LlvmPointer LlvmI64)
                    forM_ (zip [(0 :: Integer) ..] fieldVals) $ \(idx, fieldVal) -> do
                        let fieldTy = getValueType fieldVal
                        fieldAsI64 <- bitcastToPayload fieldVal fieldTy
                        fieldPtr <- saveTmp (LlvmGetElementPtr LlvmI64 arrPtr [LlvmLiteral LlvmI64 (show idx)] True) (LlvmPointer LlvmI64)
                        tell [LlvmStore fieldAsI64 fieldPtr]
                    -- Convert pointer to i64 for payload
                    payloadVal <- saveTmp (LlvmPtrToInt arrPtr LlvmI64) LlvmI64
                    saveTmp (LlvmInsertValue resultTy withTag payloadVal 1) resultTy
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
    -- For primitive types like i1 (Bool), i8, i32, i64, the value IS the tag
    -- Only extract from aggregate types (tagged ADTs)
    case aggTy of
        LlvmI1 ->
            if resultTy == LlvmI1
                then saveTmp (LlvmIdentityCast av) resultTy
                else saveTmp (LlvmZExt av resultTy) resultTy
        LlvmI8 ->
            if resultTy == LlvmI8
                then saveTmp (LlvmIdentityCast av) resultTy
                else saveTmp (LlvmZExt av resultTy) resultTy
        LlvmI32 ->
            -- Primitive Int: the value itself is used for switching
            if resultTy == LlvmI32
                then saveTmp (LlvmIdentityCast av) resultTy
                else saveTmp (LlvmSExt av resultTy) resultTy
        LlvmI64 ->
            -- Primitive 64-bit int: the value itself is used for switching
            if resultTy == LlvmI64
                then saveTmp (LlvmIdentityCast av) resultTy
                else saveTmp (LlvmTrunc av resultTy) resultTy
        LlvmAnonymous _ -> saveTmp (LlvmExtractValue aggTy av 0) resultTy
        _ -> saveTmp (LlvmExtractValue aggTy av 0) resultTy
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
            pure $ LlvmGlobal (LT.LlvmPointer dictStructType) dictGlobalName
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
            (LlvmPointer fnPtrType)

    fnPtr <- saveTmp (LlvmLoad methodFieldPtr) fnPtrType

    if resultTy == LlvmVoid
        then do
            tell [LlvmCallStmt fnPtr resultTy compiledArgs]
            pure $ LlvmUndef LlvmVoid
        else saveTmp (LlvmCall fnPtr resultTy compiledArgs) resultTy

-- Lazy duplication: create a SUP node that lazily clones when projections are used
-- soma_dup(label, value) -> SUP handle (ptr)
-- IMPORTANT: The SUP handle must be kept as i64 to preserve the full pointer value.
-- The result type from the IR may be i32 (Int), but we return i64 and let the
-- projection ops handle the final conversion after extracting the actual value.
--
-- Tagged pointer representation:
-- - TAG_PTR (0): Heap pointer (8-byte aligned, so low 3 bits are 0)
-- - TAG_INT (1): Small integer (value << 3) | 1
-- Integers must be tagged so the runtime can distinguish them from pointers.
compileOp (OpDup label value) resultTy = do
    llValue <- compileOperand value
    let valueTy = getValueType llValue
    -- Cast value to i8* (void*) for the generic dup function
    -- For integers: create tagged representation (value << 3) | TAG_INT
    voidPtr <- case valueTy of
        LlvmPointer _ -> saveTmp (LlvmBitcast llValue (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
        _ -> do
            -- Non-pointer types (integers, bools) use tagged pointer representation.
            -- TAG_INT = 1, so we do (value << 3) | 1
            extended <- case valueTy of
                LlvmI64 -> pure llValue
                LlvmI32 -> saveTmp (LlvmSExt llValue LlvmI64) LlvmI64
                LlvmI8 -> saveTmp (LlvmSExt llValue LlvmI64) LlvmI64
                LlvmI1 -> saveTmp (LlvmZExt llValue LlvmI64) LlvmI64
                _ -> saveTmp (LlvmSExt llValue LlvmI64) LlvmI64
            -- Shift left by 3 and OR with TAG_INT (1)
            shifted <- saveTmp (LlvmShl LlvmI64 extended (LlvmLiteral LlvmI64 "3")) LlvmI64
            tagged <- saveTmp (LlvmAdd LlvmI64 shifted (LlvmLiteral LlvmI64 "1")) LlvmI64
            saveTmp (LlvmIntToPtr tagged (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
    let labelVal = LlvmLiteral LlvmI32 (show label)
    -- Call soma_dup(label, value) -> returns SUP handle (i8*)
    dupFunc <- useDep cruntimeSomaDup
    supHandle <- saveTmp (LlvmCall dupFunc (LlvmPointer LlvmI8) [labelVal, voidPtr]) (LlvmPointer LlvmI8)
    -- Convert SUP handle to i64 to preserve full pointer value on 64-bit systems.
    -- Do NOT truncate to i32 even if resultTy is i32 - the projections expect i64.
    case resultTy of
        LlvmPointer _ -> saveTmp (LlvmBitcast supHandle resultTy) resultTy
        LlvmI64 -> saveTmp (LlvmPtrToInt supHandle LlvmI64) LlvmI64
        -- For smaller int types, still return i64 to preserve the pointer
        -- The projection ops will handle conversion to the actual value type
        _ -> saveTmp (LlvmPtrToInt supHandle LlvmI64) LlvmI64

-- First projection from SUP handle: soma_proj0(handle) -> value
-- soma_proj0 takes i64 (SomaValue) and returns i64 (SomaValue)
compileOp (OpDupProj0 handle) resultTy = do
    llHandle <- compileOperand handle
    let handleTy = getValueType llHandle
    -- Convert handle to i64 (SomaValue)
    i64Handle <- case handleTy of
        LlvmI64 -> pure llHandle
        LlvmPointer _ -> saveTmp (LlvmPtrToInt llHandle LlvmI64) LlvmI64
        _ -> saveTmp (LlvmSExt llHandle LlvmI64) LlvmI64
    -- Call soma_proj0(handle) -> value (i64)
    proj0Func <- useDep cruntimeSomaProj0
    result <- saveTmp (LlvmCall proj0Func LlvmI64 [i64Handle]) LlvmI64
    -- Convert result to expected type
    -- For pointers, use inttoptr directly (TAG_PTR = 0, so no shift needed)
    -- For integers, untag by shifting right 3 (TAG_INT = 1, format is (value << 3) | 1)
    case resultTy of
        LlvmI64 -> do
            -- Untag: shift right by 3 to recover the original integer
            saveTmp (LlvmLShr LlvmI64 result (LlvmLiteral LlvmI64 "3")) LlvmI64
        LlvmPointer _ -> saveTmp (LlvmIntToPtr result resultTy) resultTy
        _ -> do
            -- Untag: shift right by 3 first, then truncate
            untagged <- saveTmp (LlvmLShr LlvmI64 result (LlvmLiteral LlvmI64 "3")) LlvmI64
            saveTmp (LlvmTrunc untagged resultTy) resultTy

-- Second projection from SUP handle: soma_proj1(handle) -> value
-- soma_proj1 takes i64 (SomaValue) and returns i64 (SomaValue)
compileOp (OpDupProj1 handle) resultTy = do
    llHandle <- compileOperand handle
    let handleTy = getValueType llHandle
    -- Convert handle to i64 (SomaValue)
    i64Handle <- case handleTy of
        LlvmI64 -> pure llHandle
        LlvmPointer _ -> saveTmp (LlvmPtrToInt llHandle LlvmI64) LlvmI64
        _ -> saveTmp (LlvmSExt llHandle LlvmI64) LlvmI64
    -- Call soma_proj1(handle) -> value (i64)
    proj1Func <- useDep cruntimeSomaProj1
    result <- saveTmp (LlvmCall proj1Func LlvmI64 [i64Handle]) LlvmI64
    -- Convert result to expected type
    -- For pointers, use inttoptr directly (TAG_PTR = 0, so no shift needed)
    -- For integers, untag by shifting right 3 (TAG_INT = 1, format is (value << 3) | 1)
    case resultTy of
        LlvmI64 -> do
            -- Untag: shift right by 3 to recover the original integer
            saveTmp (LlvmLShr LlvmI64 result (LlvmLiteral LlvmI64 "3")) LlvmI64
        LlvmPointer _ -> saveTmp (LlvmIntToPtr result resultTy) resultTy
        _ -> do
            -- Untag: shift right by 3 first, then truncate
            untagged <- saveTmp (LlvmLShr LlvmI64 result (LlvmLiteral LlvmI64 "3")) LlvmI64
            saveTmp (LlvmTrunc untagged resultTy) resultTy

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
    allocClosureFunc <- useDep cruntimeSomaAllocClosure
    let arityVal = LlvmLiteral LlvmI8 "0"
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
    allocClosureFunc <- useDep cruntimeSomaAllocClosure
    let arityVal = LlvmLiteral LlvmI8 (show arity)
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
    getEnvFunc <- useDep cruntimeSomaClosureGetEnv
    let idxVal = LlvmLiteral LlvmI16 (show idx)
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
-- Direct GEP access is optimal: single pointer arithmetic + load, no call overhead.
-- Closure structure: { i8 tag, i8 arity, i16 env_size, i32 padding, ptr func_ptr }
compileOp (OpClosureGetFunc closureOp) resultTy = do
    closureStructType <- useType cruntimeSomaClosureType
    llClosure <- compileOperand closureOp
    voidClosure <- case getValueType llClosure of
        LlvmPointer LlvmI8 -> pure llClosure
        LlvmPointer _ -> saveTmp (LlvmBitcast llClosure (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
        _ -> saveTmp (LlvmIntToPtr llClosure (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
    -- GEP to func_ptr field (index 4 in the padded struct)
    funcPtrPtr <- saveTmp (LlvmGetElementPtr closureStructType voidClosure [LlvmLiteral LlvmI32 "0", LlvmLiteral LlvmI32 "4"] True) (LlvmPointer (LlvmPointer LlvmI8))
    result <- saveTmp (LlvmLoad funcPtrPtr) (LlvmPointer LlvmI8)
    -- Cast to result type if needed
    if resultTy == LlvmPointer LlvmI8
        then pure result
        else saveTmp (LlvmBitcast result resultTy) resultTy

-- Specialized closure duplication operations

-- OpDupClosure: Create a SUP node for closure duplication
-- Semantically equivalent to OpDup but carries slot type info for specialized projections.
-- The SUP creation is identical to OpDup - specialization happens in OpDupClosureProj0/1
-- which use the slot info to generate inline cloning code with proper SUP wrapping.
-- IMPORTANT: The SUP handle must be kept as i64 to preserve the full pointer value.
compileOp (OpDupClosure label closureOp _slotInfo) resultTy = do
    llClosure <- compileOperand closureOp
    let closureTy = getValueType llClosure
    -- Cast closure to i8* (void*) for the generic dup function
    -- For integers, we need to tag them: (value << 3) | TAG_INT where TAG_INT = 1
    voidPtr <- case closureTy of
        LlvmPointer _ -> saveTmp (LlvmBitcast llClosure (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
        _ -> do
            -- For integers: create tagged representation (value << 3) | TAG_INT
            extended <- case closureTy of
                LlvmI64 -> pure llClosure
                LlvmI32 -> saveTmp (LlvmSExt llClosure LlvmI64) LlvmI64
                LlvmI8 -> saveTmp (LlvmSExt llClosure LlvmI64) LlvmI64
                LlvmI1 -> saveTmp (LlvmZExt llClosure LlvmI64) LlvmI64
                _ -> saveTmp (LlvmSExt llClosure LlvmI64) LlvmI64
            shifted <- saveTmp (LlvmShl LlvmI64 extended (LlvmLiteral LlvmI64 "3")) LlvmI64
            tagged <- saveTmp (LlvmAdd LlvmI64 shifted (LlvmLiteral LlvmI64 "1")) LlvmI64
            saveTmp (LlvmIntToPtr tagged (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
    let labelVal = LlvmLiteral LlvmI32 (show label)
    -- Call soma_dup(label, closure) -> returns SUP handle (i8*)
    somaDup <- useDep cruntimeSomaDup
    supHandle <- saveTmp (LlvmCall somaDup (LlvmPointer LlvmI8) [labelVal, voidPtr]) (LlvmPointer LlvmI8)
    -- Convert SUP handle to i64 to preserve full pointer value on 64-bit systems.
    case resultTy of
        LlvmPointer _ -> saveTmp (LlvmBitcast supHandle resultTy) resultTy
        LlvmI64 -> saveTmp (LlvmPtrToInt supHandle LlvmI64) LlvmI64
        _ -> saveTmp (LlvmPtrToInt supHandle LlvmI64) LlvmI64

-- OpDupClosureProj0: First projection of closure SUP
-- Returns the original closure. This is the "happy path" - no cloning needed.
-- The slotInfo is carried for consistency but not used here since we return original.
-- soma_proj0 takes i64 (SomaValue) and returns i64 (SomaValue)
compileOp (OpDupClosureProj0 handleOp _envSize _slotInfo) resultTy = do
    llHandle <- compileOperand handleOp
    let handleTy = getValueType llHandle
    -- Convert handle to i64 (SomaValue)
    i64Handle <- case handleTy of
        LlvmI64 -> pure llHandle
        LlvmPointer _ -> saveTmp (LlvmPtrToInt llHandle LlvmI64) LlvmI64
        _ -> saveTmp (LlvmSExt llHandle LlvmI64) LlvmI64
    -- Call soma_proj0(handle) -> value (i64)
    proj0Func <- useDep cruntimeSomaProj0
    result <- saveTmp (LlvmCall proj0Func LlvmI64 [i64Handle]) LlvmI64
    -- Convert result to expected type
    -- For pointers, use inttoptr directly (TAG_PTR = 0, so no shift needed)
    -- For integers, untag by shifting right 3 (TAG_INT = 1, format is (value << 3) | 1)
    case resultTy of
        LlvmI64 -> do
            -- Untag: shift right by 3 to recover the original integer
            saveTmp (LlvmLShr LlvmI64 result (LlvmLiteral LlvmI64 "3")) LlvmI64
        LlvmPointer _ -> saveTmp (LlvmIntToPtr result resultTy) resultTy
        _ -> do
            -- Untag: shift right by 3 first, then truncate
            untagged <- saveTmp (LlvmLShr LlvmI64 result (LlvmLiteral LlvmI64 "3")) LlvmI64
            saveTmp (LlvmTrunc untagged resultTy) resultTy

-- OpDupClosureProj1: Second projection of closure SUP with HVM-style SUP propagation
-- When both projections are accessed, we clone the closure and wrap closure-typed
-- env slots in SUPs (using fresh labels) for lazy nested cloning.
--
-- This generates fully inline specialized code that:
-- 1. Checks SUP state and handles the state machine
-- 2. Returns cached value if already accessed
-- 3. For first proj1 access (after proj0): allocates new closure, copies header,
--    and for each env slot either wraps in SUP (closure slot) or copies directly
--
-- Benefits over calling soma_proj1:
-- - No function call overhead
-- - Compile-time knowledge of slot types (no runtime tag checks per slot)
-- - Unrolled loop over slots (no loop overhead)
--
-- IMPORTANT: When envSize is unknown (0) but we're duplicating a closure that might
-- have env slots, we must fall back to soma_proj1 which reads env_size at runtime.
-- The inline code only works when we know the exact env layout at compile time.
compileOp (OpDupClosureProj1 handleOp envSize slotInfo) resultTy = do
    llHandle <- compileOperand handleOp
    let handleTy = getValueType llHandle

    -- When envSize is unknown (0), fall back to runtime function which reads
    -- env_size from the closure header. This handles closures from function calls
    -- where we don't have compile-time knowledge of the env layout.
    -- When envSize > 0, we know the exact layout and can generate optimized inline code.
    result <-
        if envSize == 0 && null slotInfo
            then do
                -- Fall back to runtime - closure has unknown env layout
                -- soma_proj1 takes i64 (SomaValue) and returns i64 (SomaValue)
                i64Handle <- case handleTy of
                    LlvmI64 -> pure llHandle
                    LlvmPointer _ -> saveTmp (LlvmPtrToInt llHandle LlvmI64) LlvmI64
                    _ -> saveTmp (LlvmSExt llHandle LlvmI64) LlvmI64
                proj1Func <- useDep cruntimeSomaProj1
                i64Result <- saveTmp (LlvmCall proj1Func LlvmI64 [i64Handle]) LlvmI64
                -- Convert back to ptr for the rest of the code
                saveTmp (LlvmIntToPtr i64Result (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
            else do
                -- Generate inline specialized cloning code (needs ptr)
                voidHandle <- case handleTy of
                    LlvmPointer LlvmI8 -> pure llHandle
                    LlvmPointer _ -> saveTmp (LlvmBitcast llHandle (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
                    _ -> saveTmp (LlvmIntToPtr llHandle (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
                compileInlineClosureProj1 voidHandle envSize slotInfo
    castResult result resultTy
  where
    castResult result ty
        | ty == LlvmPointer LlvmI8 = pure result
        | otherwise = case ty of
            LlvmPointer _ -> saveTmp (LlvmBitcast result ty) ty
            _ -> saveTmp (LlvmPtrToInt result ty) ty

    -- Generate inline specialized closure cloning for proj1
    -- This implements the full SUP state machine inline:
    --   if (tag == SUP_TAG_FRESH) -> mark PROJ1, return value
    --   if (tag == SUP_TAG_PROJ0) -> mark BOTH, clone closure with SUP wrapping
    --   else -> return cached proj1
    compileInlineClosureProj1 :: LlvmValue -> Int -> SlotInfo -> IrGen LlvmValue
    compileInlineClosureProj1 supHandle envSz slots = do
        -- Load SUP tag (offset 0)
        supTagPtr <- saveTmp (LlvmGetElementPtr LlvmI8 supHandle [LlvmLiteral LlvmI64 "0"] False) (LlvmPointer LlvmI8)
        supTag <- saveTmp (LlvmLoad supTagPtr) LlvmI8

        -- Load SUP value pointer (offset 8: after tag[1] + pad[3] + label[4])
        supValuePtr <- saveTmp (LlvmGetElementPtr LlvmI8 supHandle [LlvmLiteral LlvmI64 "8"] False) (LlvmPointer (LlvmPointer LlvmI8))
        supValue <- saveTmp (LlvmLoad supValuePtr) (LlvmPointer LlvmI8)

        -- Load SUP proj1 cache pointer (offset 24: after tag[1] + pad[3] + label[4] + value[8] + proj0[8])
        supProj1Ptr <- saveTmp (LlvmGetElementPtr LlvmI8 supHandle [LlvmLiteral LlvmI64 "24"] False) (LlvmPointer (LlvmPointer LlvmI8))

        -- Check if tag == SUP_TAG_FRESH (128)
        isFresh <- saveTmp (LlvmICmp LlvmI8 "eq" supTag (LlvmLiteral LlvmI8 "128")) LlvmI1

        -- Generate unique labels for branches
        freshLabel <- freshBlockName "proj1_fresh"
        checkProj0Label <- freshBlockName "proj1_check_proj0"
        cloneLabel <- freshBlockName "proj1_clone"
        cachedLabel <- freshBlockName "proj1_cached"
        doneLabel <- freshBlockName "proj1_done"

        -- Branch: if fresh, go to fresh path; else check proj0
        tell [LlvmBrCond isFresh freshLabel checkProj0Label]

        -- Fresh path: first access via proj1, mark PROJ1 and return value
        tell [LlvmLabel freshLabel]
        tell [LlvmStore (LlvmLiteral LlvmI8 "130") supTagPtr] -- SUP_TAG_PROJ1 = 130
        tell [LlvmStore supValue supProj1Ptr] -- Cache the value
        tell [LlvmBr doneLabel]
        let freshResult = supValue

        -- Check proj0 path: if tag == SUP_TAG_PROJ0 (129), need to clone
        tell [LlvmLabel checkProj0Label]
        isProj0First <- saveTmp (LlvmICmp LlvmI8 "eq" supTag (LlvmLiteral LlvmI8 "129")) LlvmI1
        tell [LlvmBrCond isProj0First cloneLabel cachedLabel]

        -- Clone path: proj0 was accessed first, now we need to clone
        tell [LlvmLabel cloneLabel]
        tell [LlvmStore (LlvmLiteral LlvmI8 "131") supTagPtr] -- SUP_TAG_BOTH = 131

        -- Allocate new closure: 16 (header) + envSize * 8 bytes
        allocClosureFunc <- useDep cruntimeSomaPoolAllocClosure
        newClosure <- saveTmp (LlvmCall allocClosureFunc (LlvmPointer LlvmI8) [LlvmLiteral LlvmI16 (show envSz)]) (LlvmPointer LlvmI8)

        -- Copy header (16 bytes) using memcpy
        memcpyFunc <- useDep memcpyDependency
        _ <- saveTmp (LlvmCall memcpyFunc (LlvmPointer LlvmI8) [newClosure, supValue, LlvmLiteral LlvmI64 "16"]) (LlvmPointer LlvmI8)

        -- Copy/wrap each env slot
        -- For closure slots: wrap in SUP with fresh label
        -- For non-closure slots: direct copy
        mapM_ (copyOrWrapSlot supValue newClosure) [0 .. envSz - 1]

        -- Cache the cloned closure
        tell [LlvmStore newClosure supProj1Ptr]
        tell [LlvmBr doneLabel]
        let cloneResult = newClosure

        -- Cached path: already accessed, return cached proj1
        tell [LlvmLabel cachedLabel]
        cachedValue <- saveTmp (LlvmLoad supProj1Ptr) (LlvmPointer LlvmI8)
        tell [LlvmBr doneLabel]

        -- Done: phi node to merge results
        tell [LlvmLabel doneLabel]
        saveTmp
            ( LlvmPhi
                (LlvmPointer LlvmI8)
                [ (freshResult, freshLabel)
                , (cloneResult, cloneLabel)
                , (cachedValue, cachedLabel)
                ]
            )
            (LlvmPointer LlvmI8)
      where
        -- Copy or wrap a single env slot
        copyOrWrapSlot :: LlvmValue -> LlvmValue -> Int -> IrGen ()
        copyOrWrapSlot srcClosure dstClosure slotIdx = do
            let slotOffset = 16 + slotIdx * 8
            let offsetVal = LlvmLiteral LlvmI64 (show slotOffset)

            -- Get source and destination slot pointers
            srcSlotPtr <- saveTmp (LlvmGetElementPtr LlvmI8 srcClosure [offsetVal] False) (LlvmPointer (LlvmPointer LlvmI8))
            dstSlotPtr <- saveTmp (LlvmGetElementPtr LlvmI8 dstClosure [offsetVal] False) (LlvmPointer (LlvmPointer LlvmI8))

            -- Load source value
            srcVal <- saveTmp (LlvmLoad srcSlotPtr) (LlvmPointer LlvmI8)

            -- Check if this slot is a closure type (from compile-time slotInfo)
            let isClosureSlot = slotIdx `elem` [idx | (idx, True) <- slots]

            if isClosureSlot
                then do
                    -- Closure slot: wrap in SUP for lazy nested cloning
                    freshLabelFunc <- useDep cruntimeSomaFreshLabel
                    freshLbl <- saveTmp (LlvmCall freshLabelFunc LlvmI32 []) LlvmI32

                    dupFunc <- useDep cruntimeSomaDup
                    supForSlot <- saveTmp (LlvmCall dupFunc (LlvmPointer LlvmI8) [freshLbl, srcVal]) (LlvmPointer LlvmI8)

                    tell [LlvmStore supForSlot dstSlotPtr]
                else do
                    -- Non-closure slot: direct copy
                    tell [LlvmStore srcVal dstSlotPtr]

-- OpClosureGetEnvDirect: Direct env slot access for original closures
-- Single load, no SUP projection needed
compileOp (OpClosureGetEnvDirect closureOp idx) resultTy = do
    llClosure <- compileOperand closureOp
    voidClosure <- case getValueType llClosure of
        LlvmPointer LlvmI8 -> pure llClosure
        LlvmPointer _ -> saveTmp (LlvmBitcast llClosure (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
        _ -> saveTmp (LlvmIntToPtr llClosure (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
    -- Call soma_closure_get_env(closure, index) - same as OpClosureGetEnv
    getEnvFunc <- useDep cruntimeSomaClosureGetEnv
    let idxVal = LlvmLiteral LlvmI16 (show idx)
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
    getEnvFunc <- useDep cruntimeSomaClosureGetEnv
    let idxVal = LlvmLiteral LlvmI16 (show idx)
    supHandle <- saveTmp (LlvmCall getEnvFunc (LlvmPointer LlvmI8) [voidClosure, idxVal]) (LlvmPointer LlvmI8)
    -- Project through the SUP using proj1 (clone is "second copy")
    proj1Func <- useDep cruntimeSomaProj1
    result <- saveTmp (LlvmCall proj1Func (LlvmPointer LlvmI8) [supHandle]) (LlvmPointer LlvmI8)
    -- Cast to result type if needed
    if resultTy == LlvmPointer LlvmI8
        then pure result
        else case resultTy of
            LlvmPointer _ -> saveTmp (LlvmBitcast result resultTy) resultTy
            _ -> saveTmp (LlvmPtrToInt result resultTy) resultTy

-- Parallel projection operations
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
    parProj0Func <- useDep cruntimeSomaParProj0
    let workVal = LlvmLiteral LlvmI32 (show workEstimate)
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
    parProj1Func <- useDep cruntimeSomaParProj1
    let workVal = LlvmLiteral LlvmI32 (show workEstimate)
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
    parProj0Func <- useDep cruntimeSomaParProj0
    let workVal = LlvmLiteral LlvmI32 (show workEstimate)
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
            parProj1Func <- useDep cruntimeSomaParProj1
            let workVal = LlvmLiteral LlvmI32 (show workEstimate)
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
        parProj1Func <- useDep cruntimeSomaParProj1
        let workVal = LlvmLiteral LlvmI32 (show workEstimate)
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
        freshLabelFunc <- useDep cruntimeSomaFreshLabel
        freshLabel <- saveTmp (LlvmCall freshLabelFunc LlvmI32 []) LlvmI32
        dupFunc <- useDep cruntimeSomaDup
        supForSlot <- saveTmp (LlvmCall dupFunc (LlvmPointer LlvmI8) [freshLabel, currentVal]) (LlvmPointer LlvmI8)
        tell [LlvmStore supForSlot slotPtr]
        pure closure

-- Panic: call soma_panic with message and emit unreachable
compileOp (OpPanic msg) _resultTy = do
    -- Create a global string constant for the panic message
    msgPtr <- newStrTemplate msg
    -- Note: soma_panic is not in the runtime dependencies, so we use it as a hardcoded global
    -- This is a special case for panic handling
    panicFunc <- useDep cruntimeSomaPanic
    tell [LlvmCallStmt panicFunc LlvmVoid [msgPtr]]
    -- Emit unreachable (panic never returns)
    tell [LlvmUnreachable]
    -- Return a dummy value (never reached) - use null pointer
    pure (LlvmLiteral (LlvmPointer LlvmI8) "null")

-- ============================================================================
-- INET Runtime Operations
--
-- The INET runtime uses a 64-bit Term encoding and provides parallel
-- graph reduction via work-stealing. Terms are returned directly (not indices).
-- ============================================================================

-- INET init: call inet_init(num_threads) and store in globals
-- Returns INet* which we store in g_inet
compileOp (OpGraphInit numWorkers) _resultTy = do
    -- Use inet_init_globals which sets both g_inet and g_inet_tm
    initFunc <- useDep cruntimeInetInitGlobals
    let numWorkersVal = LlvmLiteral LlvmI32 (show numWorkers)
    tell [LlvmCallStmt initFunc LlvmVoid [numWorkersVal]]
    pure (LlvmLiteral LlvmI32 "0")

-- INET shutdown: call inet_free(g_inet)
compileOp OpGraphShutdown _resultTy = do
    globalPtr <- useDep cruntimeGInet
    net <- saveTmp (LlvmLoad globalPtr) (LlvmPointer LlvmI8)
    freeFunc <- useDep cruntimeInetFree
    tell [LlvmCallStmt freeFunc LlvmVoid [net]]
    pure (LlvmLiteral LlvmI32 "0")

-- INET num: create a NUM term using inet_num_ext (non-inline wrapper)
-- inet_num packs the 48-bit value into aux+loc of the term
-- Supports both integer and pointer values (pointers are converted via ptrtoint)
compileOp (OpGraphNum valOp) _resultTy = do
    llVal <- compileOperand valOp
    -- Convert to i64 if needed (handles both integers and pointers)
    i64Val <- case getValueType llVal of
        LlvmI64 -> pure llVal
        LlvmI32 -> saveTmp (LlvmSExt llVal LlvmI64) LlvmI64
        LlvmPointer _ -> saveTmp (LlvmPtrToInt llVal LlvmI64) LlvmI64
        _ -> saveTmp (LlvmSExt llVal LlvmI64) LlvmI64
    -- Call inet_num_ext(value) -> Term (i64)
    numFunc <- useDep cruntimeInetNumExt
    saveTmp (LlvmCall numFunc LlvmI64 [i64Val]) LlvmI64

-- INET add: create OPR term with OP_ADD (0x00)
-- inet_opr(net, tm, op, a, b) -> Term
compileOp (OpGraphAdd leftOp rightOp) _resultTy = do
    llLeft <- compileOperand leftOp
    llRight <- compileOperand rightOp
    (net, tm) <- getNetAndTm
    oprFunc <- useDep cruntimeInetOpr
    let opAdd = LlvmLiteral LlvmI16 "0" -- OP_ADD
    saveTmp (LlvmCall oprFunc LlvmI64 [net, tm, opAdd, llLeft, llRight]) LlvmI64

-- INET sub: create OPR term with OP_SUB (0x01)
compileOp (OpGraphSub leftOp rightOp) _resultTy = do
    llLeft <- compileOperand leftOp
    llRight <- compileOperand rightOp
    (net, tm) <- getNetAndTm
    oprFunc <- useDep cruntimeInetOpr
    let opSub = LlvmLiteral LlvmI16 "1" -- OP_SUB
    saveTmp (LlvmCall oprFunc LlvmI64 [net, tm, opSub, llLeft, llRight]) LlvmI64

-- INET mul: create OPR term with OP_MUL (0x02)
compileOp (OpGraphMul leftOp rightOp) _resultTy = do
    llLeft <- compileOperand leftOp
    llRight <- compileOperand rightOp
    (net, tm) <- getNetAndTm
    oprFunc <- useDep cruntimeInetOpr
    let opMul = LlvmLiteral LlvmI16 "2" -- OP_MUL
    saveTmp (LlvmCall oprFunc LlvmI64 [net, tm, opMul, llLeft, llRight]) LlvmI64

-- INET div: create OPR term with OP_DIV (0x03)
compileOp (OpGraphDiv leftOp rightOp) _resultTy = do
    llLeft <- compileOperand leftOp
    llRight <- compileOperand rightOp
    (net, tm) <- getNetAndTm
    oprFunc <- useDep cruntimeInetOpr
    let opDiv = LlvmLiteral LlvmI16 "3" -- OP_DIV
    saveTmp (LlvmCall oprFunc LlvmI64 [net, tm, opDiv, llLeft, llRight]) LlvmI64

-- INET mod: create OPR term with OP_MOD (0x04)
compileOp (OpGraphMod leftOp rightOp) _resultTy = do
    llLeft <- compileOperand leftOp
    llRight <- compileOperand rightOp
    (net, tm) <- getNetAndTm
    oprFunc <- useDep cruntimeInetOpr
    let opMod = LlvmLiteral LlvmI16 "4" -- OP_MOD
    saveTmp (LlvmCall oprFunc LlvmI64 [net, tm, opMod, llLeft, llRight]) LlvmI64

-- INET call: in graph mode, we need to reduce args and call the native function directly
-- The function returns a Term (i64) that represents the graph result
compileOp (OpGraphCall fnName argOps) _resultTy = do
    modName <- asks moduleName
    llArgs <- mapM compileOperand argOps
    net <- getNet
    -- Reduce each graph argument to get native Int values
    reduceFunc <- useDep cruntimeInetReduce
    reducedArgs <- forM llArgs $ \arg -> do
        i64Val <- saveTmp (LlvmCall reduceFunc LlvmI64 [net, arg]) LlvmI64
        saveTmp (LlvmTrunc i64Val LlvmI32) LlvmI32
    -- Call the compiled function directly (it takes Int args and returns Term)
    -- Use qualified name to match the function's actual LLVM name
    let qualifiedName = qualifyWithModule modName fnName
        fnGlobal = LlvmGlobal LlvmI64 ("\"" ++ qualifiedName ++ "\"")
    saveTmp (LlvmCall fnGlobal LlvmI64 reducedArgs) LlvmI64

-- INET reduce: call inet_reduce(net, root) -> i64 result
compileOp (OpGraphReduce rootOp) resultTy = do
    llRoot <- compileOperand rootOp
    net <- getNet
    reduceFunc <- useDep cruntimeInetReduce
    i64Result <- saveTmp (LlvmCall reduceFunc LlvmI64 [net, llRoot]) LlvmI64
    -- Truncate i64 result to target type (typically i32 for Int)
    case resultTy of
        LlvmI64 -> pure i64Result
        LlvmI32 -> saveTmp (LlvmTrunc i64Result LlvmI32) LlvmI32
        _ -> saveTmp (LlvmTrunc i64Result resultTy) resultTy

-- INET extract num: get integer from a NUM term without reducing
-- Assumes term is already TAG_NUM. Calls inet_get_num_ext(term) -> i64
compileOp (OpGraphExtractNum termOp) resultTy = do
    llTerm <- compileOperand termOp
    extractFunc <- useDep cruntimeInetGetNumExt
    i64Result <- saveTmp (LlvmCall extractFunc LlvmI64 [llTerm]) LlvmI64
    case resultTy of
        LlvmI64 -> pure i64Result
        LlvmI32 -> saveTmp (LlvmTrunc i64Result LlvmI32) LlvmI32
        _ -> saveTmp (LlvmTrunc i64Result resultTy) resultTy

-- INET register func: call inet_register_func(net, name, arity, impl)
-- Note: This is only called from soma_main, so we use globals here
compileOp (OpGraphRegisterFunc name arity implOp) _resultTy = do
    llImpl <- compileOperand implOp
    -- Create string constant for function name
    namePtr <- newStrTemplate name
    net <- getNet
    registerFunc <- useDep cruntimeInetRegisterFunc
    let arityVal = LlvmLiteral LlvmI16 (show arity)
    -- Cast impl to ptr if needed
    implPtr <- case getValueType llImpl of
        LlvmPointer _ -> pure llImpl
        _ -> saveTmp (LlvmIntToPtr llImpl (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
    tell [LlvmCallStmt registerFunc LlvmVoid [net, namePtr, arityVal, implPtr]]
    -- Return dummy value (register doesn't return)
    pure (LlvmLiteral LlvmI16 "0")

-- ============================================================================
-- INET Interaction Net Node Operations
-- ============================================================================

-- INET DUP: create a DUP term and eagerly trigger interaction
-- inet_dup_eager(net, tm, label, target) -> Term (with proj slots already filled)
compileOp (OpGraphDup label targetOp) _resultTy = do
    llTarget <- compileOperand targetOp
    (net, tm) <- getNetAndTm
    dupFunc <- useDep cruntimeInetDupEager
    let labelVal = LlvmLiteral LlvmI16 (show label)
    saveTmp (LlvmCall dupFunc LlvmI64 [net, tm, labelVal, llTarget]) LlvmI64

-- INET DUP Get Proj0: read proj0 value from DUP node
-- After inet_dup_eager, the projection slots are filled.
-- proj0 slot = term_loc(dup) + 1, then inet_get(net, slot)
compileOp (OpGraphDupGetProj0 dupOp) _resultTy = do
    llDup <- compileOperand dupOp
    net <- getNet
    -- Extract location: loc = dup >> 32
    loc <- saveTmp (LlvmLShr LlvmI64 llDup (LlvmLiteral LlvmI64 "32")) LlvmI64
    -- proj0 slot = loc + 1
    proj0Slot <- saveTmp (LlvmAdd LlvmI64 loc (LlvmLiteral LlvmI64 "1")) LlvmI64
    -- Truncate to u32 (Loc type)
    proj0SlotU32 <- saveTmp (LlvmTrunc proj0Slot LlvmI32) LlvmI32
    -- Call inet_get(net, slot) -> Term
    getFunc <- useDep cruntimeInetGet
    saveTmp (LlvmCall getFunc LlvmI64 [net, proj0SlotU32]) LlvmI64

-- INET DUP Get Proj1: read proj1 value from DUP node
-- proj1 slot = term_loc(dup) + 2, then inet_get(net, slot)
compileOp (OpGraphDupGetProj1 dupOp) _resultTy = do
    llDup <- compileOperand dupOp
    net <- getNet
    -- Extract location: loc = dup >> 32
    loc <- saveTmp (LlvmLShr LlvmI64 llDup (LlvmLiteral LlvmI64 "32")) LlvmI64
    -- proj1 slot = loc + 2
    proj1Slot <- saveTmp (LlvmAdd LlvmI64 loc (LlvmLiteral LlvmI64 "2")) LlvmI64
    -- Truncate to u32 (Loc type)
    proj1SlotU32 <- saveTmp (LlvmTrunc proj1Slot LlvmI32) LlvmI32
    -- Call inet_get(net, slot) -> Term
    getFunc <- useDep cruntimeInetGet
    saveTmp (LlvmCall getFunc LlvmI64 [net, proj1SlotU32]) LlvmI64

-- INET SUP: create a SUP term with two children
-- inet_sup(net, tm, label, a, b) -> Term
compileOp (OpGraphSup label leftOp rightOp) _resultTy = do
    llLeft <- compileOperand leftOp
    llRight <- compileOperand rightOp
    (net, tm) <- getNetAndTm
    supFunc <- useDep cruntimeInetSup
    let labelVal = LlvmLiteral LlvmI16 (show label)
    saveTmp (LlvmCall supFunc LlvmI64 [net, tm, labelVal, llLeft, llRight]) LlvmI64

-- INET LAM: create a LAM term (lambda abstraction)
-- inet_lam(net, tm, var_loc, body) -> Term
compileOp (OpGraphLam varSlotOp bodyOp) _resultTy = do
    llVarSlot <- compileOperand varSlotOp
    llBody <- compileOperand bodyOp
    (net, tm) <- getNetAndTm
    -- Convert varSlot to Loc (u32)
    varLoc <- case getValueType llVarSlot of
        LlvmI32 -> pure llVarSlot
        LlvmI64 -> saveTmp (LlvmTrunc llVarSlot LlvmI32) LlvmI32
        _ -> saveTmp (LlvmTrunc llVarSlot LlvmI32) LlvmI32
    lamFunc <- useDep cruntimeInetLam
    saveTmp (LlvmCall lamFunc LlvmI64 [net, tm, varLoc, llBody]) LlvmI64

-- INET APP: create an APP term (application)
-- inet_app(net, tm, fun, arg) -> Term
compileOp (OpGraphApp fnOp argOp) _resultTy = do
    llFn <- compileOperand fnOp
    llArg <- compileOperand argOp
    (net, tm) <- getNetAndTm
    appFunc <- useDep cruntimeInetApp
    saveTmp (LlvmCall appFunc LlvmI64 [net, tm, llFn, llArg]) LlvmI64

-- INET ERA: create an ERA term (erasure/unit)
-- Just return the ERA constant (no heap allocation needed)
compileOp OpGraphEra _resultTy = do
    -- ERA is just term_new(TAG_ERA, 0, 0) = 0x14
    pure (LlvmLiteral LlvmI64 "20") -- TAG_ERA = 0x14 = 20

-- INET REF: create a REF node for lazy function expansion
-- REF nodes store the function index in aux and the argument at the location
compileOp (OpGraphRef _fnName funcIdx argOp) _resultTy = do
    llArg <- compileOperand argOp
    (net, tm) <- getNetAndTm
    refFunc <- useDep cruntimeInetRef
    let funcIdxVal = LlvmLiteral LlvmI16 (show funcIdx)
    saveTmp (LlvmCall refFunc LlvmI64 [net, tm, funcIdxVal, llArg]) LlvmI64
-- INET Closure: create a closure with captured environment
-- inet_closure(net, tm, func_idx, arity, env[], env_size) -> Term
compileOp (OpGraphClosure funcIdx arity envVals) _resultTy = do
    (net, tm) <- getNetAndTm
    -- Compile all environment values
    llEnvVals <- mapM compileOperand envVals
    let envSize = length envVals

    if envSize == 0
        then do
            -- No captures - create closure with empty env
            closureFunc <- useDep cruntimeInetClosure
            let funcIdxVal = LlvmLiteral LlvmI16 (show funcIdx)
                arityVal = LlvmLiteral LlvmI16 (show arity)
                envPtr = LlvmLiteral (LlvmPointer LlvmI64) "null"
                envSizeVal = LlvmLiteral LlvmI16 "0"
            saveTmp (LlvmCall closureFunc LlvmI64 [net, tm, funcIdxVal, arityVal, envPtr, envSizeVal]) LlvmI64
        else do
            -- Allocate stack space for env array
            let envSizeLit = LlvmLiteral LlvmI32 (show envSize)
            envArrayPtr <- saveTmp (LlvmAlloca LlvmI64 (Just envSizeLit)) (LlvmPointer LlvmI64)
            -- Store each env value
            forM_ (zip [0 ..] llEnvVals) $ \(i, llVal) -> do
                -- Get pointer to env[i]
                elemPtr <- saveTmp (LlvmGetElementPtr LlvmI64 envArrayPtr [LlvmLiteral LlvmI64 (show (i :: Int))] False) (LlvmPointer LlvmI64)
                tell [LlvmStore llVal elemPtr]
            -- Call inet_closure
            closureFunc <- useDep cruntimeInetClosure
            let funcIdxVal = LlvmLiteral LlvmI16 (show funcIdx)
                arityVal = LlvmLiteral LlvmI16 (show arity)
                envSizeVal = LlvmLiteral LlvmI16 (show envSize)
            saveTmp (LlvmCall closureFunc LlvmI64 [net, tm, funcIdxVal, arityVal, envArrayPtr, envSizeVal]) LlvmI64

-- INET Closure App: apply a closure to an argument
-- This is handled by the runtime via inet_app - APP-CLO interaction
compileOp (OpGraphClosureApp cloOp argOp) _resultTy = do
    llClo <- compileOperand cloOp
    llArg <- compileOperand argOp
    (net, tm) <- getNetAndTm
    appFunc <- useDep cruntimeInetApp
    saveTmp (LlvmCall appFunc LlvmI64 [net, tm, llClo, llArg]) LlvmI64

-- INET Closure Get Env: get value from closure environment slot
-- inet_closure_get_env(net, closure_term, index) -> Term
compileOp (OpGraphClosureGetEnv cloOp idx) _resultTy = do
    llClo <- compileOperand cloOp
    net <- getNet
    getEnvFunc <- useDep cruntimeInetClosureGetEnv
    let idxVal = LlvmLiteral LlvmI16 (show idx)
    saveTmp (LlvmCall getEnvFunc LlvmI64 [net, llClo, idxVal]) LlvmI64

-- INET CON: create a constructor/pair node
-- inet_con(net, tm, fst, snd) -> Term
compileOp (OpGraphCon fstOp sndOp) _resultTy = do
    llFst <- compileOperand fstOp
    llSnd <- compileOperand sndOp
    (net, tm) <- getNetAndTm
    conFunc <- useDep cruntimeInetCon
    saveTmp (LlvmCall conFunc LlvmI64 [net, tm, llFst, llSnd]) LlvmI64

-- INET CON Get: extract a field from a CON node
-- CON layout: [fst @ loc, snd @ loc+1]
-- term_loc(con) gives the base location, then inet_get(net, loc + idx)
compileOp (OpGraphConGet conOp fieldIdx) _resultTy = do
    llCon <- compileOperand conOp
    net <- getNet
    -- Extract location from the CON term: loc = term >> 32 (TERM_LOC_SHIFT)
    loc <- saveTmp (LlvmLShr LlvmI64 llCon (LlvmLiteral LlvmI64 "32")) LlvmI64
    -- Add field index to get the slot
    fieldLoc <- saveTmp (LlvmAdd LlvmI64 loc (LlvmLiteral LlvmI64 (show fieldIdx))) LlvmI64
    -- Truncate to u32 (Loc type)
    fieldLocU32 <- saveTmp (LlvmTrunc fieldLoc LlvmI32) LlvmI32
    -- Call inet_get(net, loc) -> Term
    getFunc <- useDep cruntimeInetGet
    saveTmp (LlvmCall getFunc LlvmI64 [net, fieldLocU32]) LlvmI64

-- Fork: spawn a parallel task
-- OpFork taskFn taskArgs: fork a function call with the given arguments
--
-- Design for optimal performance:
-- - Sequential mode: call function directly with all args (zero overhead)
-- - Parallel mode: generate a trampoline wrapper that converts i64 args to native types
--
-- The trampoline is necessary because:
-- - The runtime calls functions with SomaValue (i64) arguments
-- - But Soma functions may use i32, ptr, etc. as their native parameter types
-- - The trampoline converts i64 -> native type for each arg, calls the real function,
--   then converts the result back to i64
--
-- The result is encoded as:
-- - Parallel: task handle pointer (low bit = 0)
-- - Sequential: (result << 1) | 1 (low bit = 1 marks inline result)
-- OpJoin decodes this to either wait for task or extract inline result.
compileOp (OpFork taskFn taskArgs) resultTy = do
    llFn <- compileOperand taskFn
    llArgs <- mapM compileOperand taskArgs

    -- Ensure fn is a pointer (function pointer)
    fnPtr <- case getValueType llFn of
        LlvmPointer _ -> pure llFn
        _ -> saveTmp (LlvmIntToPtr llFn (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)

    -- Get the native types of each argument
    let argTypes = map getValueType llArgs

    -- Convert all args to i64 (SomaValue convention) for the parallel path
    i64Args <- forM llArgs $ \llArg -> case getValueType llArg of
        LlvmI64 -> pure llArg
        LlvmPointer _ -> saveTmp (LlvmPtrToInt llArg LlvmI64) LlvmI64
        LlvmI32 -> saveTmp (LlvmSExt llArg LlvmI64) LlvmI64
        LlvmI8 -> saveTmp (LlvmSExt llArg LlvmI64) LlvmI64
        LlvmI1 -> saveTmp (LlvmZExt llArg LlvmI64) LlvmI64
        _ -> saveTmp (LlvmSExt llArg LlvmI64) LlvmI64

    -- Check if parallel is enabled
    parEnabledFunc <- useDep cruntimeSomaParEnabledExport
    parEnabled <- saveTmp (LlvmCall parEnabledFunc LlvmI32 []) LlvmI32
    isParallel <- saveTmp (LlvmICmp LlvmI32 "ne" parEnabled (LlvmLiteral LlvmI32 "0")) LlvmI1

    -- Branch: parallel fork vs sequential inline
    parallelBlock <- freshBlockName "fork_parallel"
    sequentialBlock <- freshBlockName "fork_sequential"
    mergeBlock <- freshBlockName "fork_merge"

    tell [LlvmBrCond isParallel parallelBlock sequentialBlock]

    -- Parallel path
    tell [LlvmLabel parallelBlock]
    taskHandleI64 <- case i64Args of
        -- Single argument with i64 type: use soma_fork_direct (no trampoline needed)
        [singleArg] | hardHead argTypes == LlvmI64 -> do
            forkFunc <- useDep cruntimeSomaForkDirect
            taskHandle <- saveTmp (LlvmCall forkFunc (LlvmPointer LlvmI8) [fnPtr, singleArg]) (LlvmPointer LlvmI8)
            saveTmp (LlvmPtrToInt taskHandle LlvmI64) LlvmI64
        -- Multiple arguments or non-i64 single arg: generate trampoline and use soma_fork_multi
        _ -> do
            -- Generate a unique trampoline function name
            trampolineName <- freshBlockName "fork_trampoline"

            -- Generate and register the trampoline function
            generateTrampoline trampolineName fnPtr argTypes resultTy

            let numArgs = length i64Args
            -- Allocate array on stack for arguments
            let arrayTy = LlvmArray numArgs LlvmI64
            argsArray <- saveTmp (LlvmAlloca arrayTy Nothing) (LlvmPointer arrayTy)
            -- Store each argument into the array
            forM_ (zip [(0 :: Integer) ..] i64Args) $ \(idx, arg) -> do
                elemPtr <- saveTmp (LlvmGetElementPtr arrayTy argsArray [LlvmLiteral LlvmI32 "0", LlvmLiteral LlvmI32 (show idx)] True) (LlvmPointer LlvmI64)
                tell [LlvmStore arg elemPtr]
            -- Cast array pointer to i64* for the runtime call
            argsPtr <- saveTmp (LlvmBitcast argsArray (LlvmPointer LlvmI64)) (LlvmPointer LlvmI64)
            -- Get trampoline function pointer
            let trampolinePtr = LlvmGlobal (LlvmPointer LlvmI8) ("\"" ++ trampolineName ++ "\"")
            -- Call soma_fork_multi(trampoline, args, num_args)
            forkMultiFunc <- useDep cruntimeSomaForkMulti
            taskHandle <- saveTmp (LlvmCall forkMultiFunc (LlvmPointer LlvmI8) [trampolinePtr, argsPtr, LlvmLiteral LlvmI32 (show numArgs)]) (LlvmPointer LlvmI8)
            saveTmp (LlvmPtrToInt taskHandle LlvmI64) LlvmI64
    tell [LlvmBr mergeBlock]

    -- Sequential path: call function directly with original args (not i64-converted)
    tell [LlvmLabel sequentialBlock]
    -- resultTy is already the LlvmType for the return
    rawResult <- saveTmp (LlvmCall fnPtr resultTy llArgs) resultTy
    -- Convert result to i64 for encoding
    inlineResult <- case resultTy of
        LlvmI64 -> pure rawResult
        LlvmI32 -> saveTmp (LlvmSExt rawResult LlvmI64) LlvmI64
        LlvmI8 -> saveTmp (LlvmSExt rawResult LlvmI64) LlvmI64
        LlvmI1 -> saveTmp (LlvmZExt rawResult LlvmI64) LlvmI64
        LlvmPointer _ -> saveTmp (LlvmPtrToInt rawResult LlvmI64) LlvmI64
        _ -> saveTmp (LlvmSExt rawResult LlvmI64) LlvmI64
    -- Encode inline result: (result << 1) | 1
    encodedInline <- saveTmp (LlvmShl LlvmI64 inlineResult (LlvmLiteral LlvmI64 "1")) LlvmI64
    encodedInlineTagged <- saveTmp (LlvmAdd LlvmI64 encodedInline (LlvmLiteral LlvmI64 "1")) LlvmI64
    tell [LlvmBr mergeBlock]

    -- Merge
    tell [LlvmLabel mergeBlock]
    saveTmp (LlvmPhi LlvmI64 [(taskHandleI64, parallelBlock), (encodedInlineTagged, sequentialBlock)]) LlvmI64

-- Join: wait for a forked task and get its result
-- OpJoin taskHandle: if low bit is 1, decode inline result; else call soma_join(handle)
compileOp (OpJoin taskHandle) resultTy = do
    llHandle <- compileOperand taskHandle
    -- Ensure handle is i64
    i64Handle <- case getValueType llHandle of
        LlvmI64 -> pure llHandle
        LlvmPointer _ -> saveTmp (LlvmPtrToInt llHandle LlvmI64) LlvmI64
        _ -> saveTmp (LlvmSExt llHandle LlvmI64) LlvmI64

    -- Check low bit: 1 = inline result, 0 = task handle
    lowBit <- saveTmp (LlvmAnd LlvmI64 i64Handle (LlvmLiteral LlvmI64 "1")) LlvmI64
    isInline <- saveTmp (LlvmICmp LlvmI64 "ne" lowBit (LlvmLiteral LlvmI64 "0")) LlvmI1

    inlineBlock <- freshBlockName "join_inline"
    parallelBlock <- freshBlockName "join_parallel"
    mergeBlock <- freshBlockName "join_merge"

    tell [LlvmBrCond isInline inlineBlock parallelBlock]

    -- Inline path: decode result (value >> 1)
    tell [LlvmLabel inlineBlock]
    decodedResult <- saveTmp (LlvmLShr LlvmI64 i64Handle (LlvmLiteral LlvmI64 "1")) LlvmI64
    tell [LlvmBr mergeBlock]

    -- Parallel path: call soma_join
    tell [LlvmLabel parallelBlock]
    handlePtr <- saveTmp (LlvmIntToPtr i64Handle (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
    joinFunc <- useDep cruntimeSomaJoin
    joinResult <- saveTmp (LlvmCall joinFunc LlvmI64 [handlePtr]) LlvmI64
    tell [LlvmBr mergeBlock]

    -- Merge
    tell [LlvmLabel mergeBlock]
    result <- saveTmp (LlvmPhi LlvmI64 [(decodedResult, inlineBlock), (joinResult, parallelBlock)]) LlvmI64

    -- Cast to result type if needed
    case resultTy of
        LlvmI64 -> pure result
        LlvmPointer _ -> saveTmp (LlvmIntToPtr result resultTy) resultTy
        LlvmI32 -> saveTmp (LlvmTrunc result LlvmI32) LlvmI32
        LlvmI8 -> saveTmp (LlvmTrunc result LlvmI8) LlvmI8
        LlvmI1 -> saveTmp (LlvmTrunc result LlvmI1) LlvmI1
        _ -> saveTmp (LlvmTrunc result resultTy) resultTy

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

{- | Generate a trampoline wrapper function for parallel fork
The trampoline:
1. Takes a pointer to an array of i64 (SomaValue) arguments
2. Loads and converts each argument to its native type
3. Calls the real function
4. Converts the result back to i64 (SomaValue)
-}
generateTrampoline :: String -> LlvmValue -> [LlvmType] -> LlvmType -> IrGen ()
generateTrampoline name targetFn argTypes retTy = do
    -- The trampoline takes a single ptr argument (pointer to args array)
    let paramName = "args_ptr"
        params = [(paramName, LlvmPointer LlvmI64)]

    -- Generate the function body statements
    let argsPtr = LlvmRegister (LlvmPointer LlvmI64) paramName

    -- Build statements to load and convert each argument
    (convertedArgs, loadStmts) <- generateArgLoads argsPtr argTypes

    -- Call the target function
    let callInstr = LlvmCall targetFn retTy convertedArgs
        callReg = LlvmRegister retTy "call_result"
        callStmt = LlvmAssign "call_result" callInstr

    -- Convert result to i64
    (resultI64, resultStmts) <- generateResultConversion callReg retTy

    -- Return the i64 result
    let retStmt = LlvmRet LlvmI64 (Just resultI64)

    -- Create the function
    let allStmts = loadStmts ++ [callStmt] ++ resultStmts ++ [retStmt]
        block = LlvmBlock{blockName = "entry", blockStatements = allStmts}
        fn =
            LlvmFunction
                { functionName = "\"" ++ name ++ "\""
                , functionParams = params
                , functionReturnType = LlvmI64
                , functionBlocks = [block]
                , functionAttributes = [FnAttrNoUnwind]
                }

    -- Register the trampoline function
    modify (\s -> s{irFunctions = fn : irFunctions s})

-- | Generate statements to load arguments from the args array and convert to native types
generateArgLoads :: LlvmValue -> [LlvmType] -> IrGen ([LlvmValue], [LlvmStatement])
generateArgLoads argsPtr argTypes = do
    results <- forM (zip [0 ..] argTypes) $ \(idx, argTy) -> do
        let idxLit = LlvmLiteral LlvmI32 (show (idx :: Int))
            gepReg = "arg_ptr_" ++ show idx
            loadReg = "arg_i64_" ++ show idx
            convReg = "arg_" ++ show idx

        -- GEP to get pointer to this argument in the array
        let gepInstr = LlvmGetElementPtr LlvmI64 argsPtr [idxLit] True
            gepStmt = LlvmAssign gepReg gepInstr
            gepVal = LlvmRegister (LlvmPointer LlvmI64) gepReg

        -- Load the i64 value
        let loadInstr = LlvmLoad gepVal
            loadStmt = LlvmAssign loadReg loadInstr
            loadVal = LlvmRegister LlvmI64 loadReg

        -- Convert from i64 to the native type
        (convVal, convStmts) <- generateArgConversion loadVal argTy convReg

        pure (convVal, [gepStmt, loadStmt] ++ convStmts)

    let (vals, stmtLists) = unzip results
    pure (vals, concat stmtLists)

-- | Generate statements to convert an i64 value to a native type
generateArgConversion :: LlvmValue -> LlvmType -> String -> IrGen (LlvmValue, [LlvmStatement])
generateArgConversion i64Val targetTy regName = case targetTy of
    LlvmI64 ->
        -- No conversion needed
        pure (i64Val, [])
    LlvmI32 -> do
        -- Truncate i64 to i32
        let instr = LlvmTrunc i64Val LlvmI32
            stmt = LlvmAssign regName instr
            result = LlvmRegister LlvmI32 regName
        pure (result, [stmt])
    LlvmI8 -> do
        -- Truncate i64 to i8
        let instr = LlvmTrunc i64Val LlvmI8
            stmt = LlvmAssign regName instr
            result = LlvmRegister LlvmI8 regName
        pure (result, [stmt])
    LlvmI1 -> do
        -- Truncate i64 to i1
        let instr = LlvmTrunc i64Val LlvmI1
            stmt = LlvmAssign regName instr
            result = LlvmRegister LlvmI1 regName
        pure (result, [stmt])
    LlvmPointer innerTy -> do
        -- inttoptr i64 to pointer
        let instr = LlvmIntToPtr i64Val (LlvmPointer innerTy)
            stmt = LlvmAssign regName instr
            result = LlvmRegister (LlvmPointer innerTy) regName
        pure (result, [stmt])
    _ -> do
        -- Default: truncate to i32 (conservative)
        let instr = LlvmTrunc i64Val LlvmI32
            stmt = LlvmAssign regName instr
            result = LlvmRegister LlvmI32 regName
        pure (result, [stmt])

-- | Generate statements to convert a native result to i64
generateResultConversion :: LlvmValue -> LlvmType -> IrGen (LlvmValue, [LlvmStatement])
generateResultConversion resultVal retTy = case retTy of
    LlvmI64 ->
        -- No conversion needed
        pure (resultVal, [])
    LlvmI32 -> do
        -- Sign-extend i32 to i64
        let instr = LlvmSExt resultVal LlvmI64
            stmt = LlvmAssign "result_i64" instr
            result = LlvmRegister LlvmI64 "result_i64"
        pure (result, [stmt])
    LlvmI8 -> do
        -- Sign-extend i8 to i64
        let instr = LlvmSExt resultVal LlvmI64
            stmt = LlvmAssign "result_i64" instr
            result = LlvmRegister LlvmI64 "result_i64"
        pure (result, [stmt])
    LlvmI1 -> do
        -- Zero-extend i1 to i64
        let instr = LlvmZExt resultVal LlvmI64
            stmt = LlvmAssign "result_i64" instr
            result = LlvmRegister LlvmI64 "result_i64"
        pure (result, [stmt])
    LlvmPointer _ -> do
        -- ptrtoint pointer to i64
        let instr = LlvmPtrToInt resultVal LlvmI64
            stmt = LlvmAssign "result_i64" instr
            result = LlvmRegister LlvmI64 "result_i64"
        pure (result, [stmt])
    LlvmVoid ->
        -- Void return - return 0
        pure (LlvmLiteral LlvmI64 "0", [])
    _ -> do
        -- Default: sign-extend to i64
        let instr = LlvmSExt resultVal LlvmI64
            stmt = LlvmAssign "result_i64" instr
            result = LlvmRegister LlvmI64 "result_i64"
        pure (result, [stmt])
