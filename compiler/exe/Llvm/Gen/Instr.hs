module Llvm.Gen.Instr (
    compileInstr,
    compileTerminator,
) where

import Alloy.Ir
import Control.Monad.Reader (asks)
import Control.Monad.Writer.Class (MonadWriter (tell))
import Llvm.Gen.CRuntime (
    cruntimeGInet,
    cruntimeInetFree,
    cruntimeInetInitGlobals,
    cruntimeInetRegisterFunc,
    cruntimeSomaClosureSetEnv,
    cruntimeSomaEraFree,
 )
import Llvm.Gen.Core
import Llvm.Gen.Externals (useDep)
import Llvm.Gen.Op (compileOp)
import Llvm.Gen.Operands (compileOperand)
import Llvm.Gen.Templates (newStrTemplate)
import Llvm.Gen.TypeConversion (convertType)
import Llvm.Instructions
import Llvm.Types (LlvmType (..), deref)
import Llvm.Values (LlvmValue (..), getValueType)
import Project.Name (nameToLLVM, nameToString)

compileInstr :: AInstr -> IrGen ()
compileInstr (ILet letName letTy letOp) = do
    let llTy = convertType letTy
    resultVal <- compileOp letOp llTy
    recordSubstitution (nameToString letName) resultVal
compileInstr (IEffect (EffStore value addr)) = do
    llValue <- compileOperand value
    llAddr <- compileOperand addr
    tell [LlvmStore llValue llAddr]
compileInstr (IEffect (EffStoreIndex array index value)) = do
    llArray <- compileOperand array
    llIndex <- compileOperand index
    llValue <- compileOperand value
    let arrayPointeeTy =
            case getValueType llArray of
                ptrTy -> deref ptrTy
    elemPtrReg <- saveTmp (LlvmGetElementPtr arrayPointeeTy llArray [llIndex] True) (getValueType llArray)
    tell [LlvmStore llValue elemPtrReg]
compileInstr (IEffect (EffDrop value)) = do
    -- ERA node: free heap-allocated value
    -- Call runtime function that:
    --   1. Checks if the value is heap-allocated (via type tag)
    --   2. Recursively frees children
    --   3. Frees the node itself
    -- For stack values, the runtime function is a no-op
    llValue <- compileOperand value
    let valueTy = getValueType llValue
    -- For pointer types, call the free function
    -- For non-pointer types (stack allocated), skip
    case valueTy of
        LlvmPointer _ -> do
            -- Cast to i8* (void*) for the generic free function
            voidPtr <- saveTmp (LlvmBitcast llValue (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
            -- Call soma_era_free(ptr) - will recursively free heap nodes
            freeFunc <- useDep cruntimeSomaEraFree
            tell [LlvmCallStmt freeFunc LlvmVoid [voidPtr]]
        _ ->
            -- Stack-allocated value, no free needed
            pure ()
compileInstr (IEffect (EffClosureSetEnv closure idx value)) = do
    -- Set a closure environment slot
    -- soma_closure_set_env(closure, index, value)
    llClosure <- compileOperand closure
    llValue <- compileOperand value
    -- Ensure closure is i8*
    voidClosure <- case getValueType llClosure of
        LlvmPointer LlvmI8 -> pure llClosure
        LlvmPointer _ -> saveTmp (LlvmBitcast llClosure (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
        _ -> saveTmp (LlvmIntToPtr llClosure (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)

    -- Tag the value to create a SomaValue (i64)
    taggedValue <- case getValueType llValue of
        LlvmPointer _ ->
            -- Pointers have tag 0, just cast to i64
            saveTmp (LlvmPtrToInt llValue LlvmI64) LlvmI64
        LlvmI1 -> do
            -- Booleans are TAG_BOOL (2) with payload 0 or 1
            zext <- saveTmp (LlvmZExt llValue LlvmI64) LlvmI64
            let shiftAmount = LlvmLiteral LlvmI64 "3"
            shifted <- saveTmp (LlvmShl LlvmI64 zext shiftAmount) LlvmI64
            let tag = LlvmLiteral LlvmI64 "2"
            saveTmp (LlvmAdd LlvmI64 shifted tag) LlvmI64
        _ -> do
            -- Integers are TAG_INT (1)
            -- Sign extend to i64, shift left by 3, then OR with tag 1
            sext <- saveTmp (LlvmSExt llValue LlvmI64) LlvmI64
            let shiftAmount = LlvmLiteral LlvmI64 "3"
            shifted <- saveTmp (LlvmShl LlvmI64 sext shiftAmount) LlvmI64
            let tag = LlvmLiteral LlvmI64 "1"
            saveTmp (LlvmAdd LlvmI64 shifted tag) LlvmI64

    -- Call soma_closure_set_env(closure, index, taggedValue)
    setEnvFunc <- useDep cruntimeSomaClosureSetEnv
    let idxVal = LlvmLiteral LlvmI16 (show idx)
    tell [LlvmCallStmt setEnvFunc LlvmVoid [voidClosure, idxVal, taggedValue]]
compileInstr (IEffect (EffGraphInit numWorkers)) = do
    -- Initialize INET runtime using inet_init_globals which sets both g_inet and g_inet_tm
    initFunc <- useDep cruntimeInetInitGlobals
    let numWorkersVal = LlvmLiteral LlvmI32 (show numWorkers)
    tell [LlvmCallStmt initFunc LlvmVoid [numWorkersVal]]
compileInstr (IEffect EffGraphShutdown) = do
    -- Shutdown INET runtime
    globalPtr <- useDep cruntimeGInet
    netPtr <- saveTmp (LlvmLoad globalPtr) (LlvmPointer LlvmI8)
    freeFunc <- useDep cruntimeInetFree
    tell [LlvmCallStmt freeFunc LlvmVoid [netPtr]]
compileInstr (IEffect (EffGraphRegisterFunc name arity implOp)) = do
    -- Register a function with the INET runtime
    llImpl <- compileOperand implOp
    -- Get global net pointer
    globalPtr <- useDep cruntimeGInet
    netPtr <- saveTmp (LlvmLoad globalPtr) (LlvmPointer LlvmI8)
    -- Create string constant for function name using newStrTemplate
    namePtr <- newStrTemplate (nameToLLVM name)
    let arityVal = LlvmLiteral LlvmI16 (show arity)
    registerFunc <- useDep cruntimeInetRegisterFunc
    -- Cast function pointer to i8*
    implPtr <- saveTmp (LlvmBitcast llImpl (LlvmPointer LlvmI8)) (LlvmPointer LlvmI8)
    tell [LlvmCallStmt registerFunc LlvmVoid [netPtr, namePtr, arityVal, implPtr]]

compileTerminator :: ATerminator -> IrGen ()
compileTerminator (ARet Nothing) = do
    tell [LlvmRet LlvmVoid Nothing]
compileTerminator (ARet (Just operand)) = do
    llvmOp <- compileOperand operand
    let ty = getValueType llvmOp
    if ty == LlvmVoid
        then tell [LlvmRet LlvmVoid Nothing]
        else tell [LlvmRet ty (Just llvmOp)]
compileTerminator (ABr target _args) = do
    -- todo: implement proper block parameter passing
    tell [LlvmBr (nameToString target)]
compileTerminator (ACondBr cond trueBlock _trueArgs falseBlock _falseArgs) = do
    llvmCond <- compileOperand cond
    -- todo: handle block arguments
    tell [LlvmBrCond llvmCond (nameToString trueBlock) (nameToString falseBlock)]
compileTerminator (ASwitch scrutinee cases maybeDefault) = do
    llvmScrutinee <- compileOperand scrutinee
    let scrutineeTy = getValueType llvmScrutinee
    let llvmCases = [(LlvmLiteral scrutineeTy (show tag), nameToString label) | (tag, label) <- cases]

    let defaultLabel = case maybeDefault of
            Just lbl -> nameToString lbl
            Nothing -> case cases of
                (_, lbl) : _ -> nameToString lbl
                [] -> "unreachable_default"

    tell [LlvmSwitch llvmScrutinee defaultLabel llvmCases]
compileTerminator AUnreachable = do
    tell [LlvmUnreachable]
