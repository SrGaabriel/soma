{-# LANGUAGE FlexibleContexts #-}

module Llvm.Gen.Intrinsics (
    compileIntrinsic,
    isIntrinsic,
) where

import Alloy.Ir (AOperand (..))
import Alloy.Naming (qualifyWithModule)
import Control.Monad.Reader (asks)
import Control.Monad.State (gets)
import Control.Monad.Writer.Class (tell)
import Llvm.Gen.Core (IrGen, IrGenEnv (..), IrGenState (..), freshBlockName, freshNamedReg, saveToNamedReg, saveTmp)
import Llvm.Gen.Externals (mallocDependency, printfDependency, putsDependency, strcpyDependency, strlenDependency, useDep)
import Llvm.Gen.Operands (compileOperand)
import Llvm.Gen.Templates (newStrTemplate)
import Llvm.Instructions (LlvmInstruction (..), LlvmStatement (..))
import Llvm.Types (LlvmType (..))
import Llvm.Values (LlvmValue (..), getValueType, intLiteral, longLiteral)

isIntrinsic :: String -> Bool
isIntrinsic "println" = True
isIntrinsic "map" = True
isIntrinsic "for" = True
isIntrinsic "strcat" = True
isIntrinsic "int_to_string" = True
isIntrinsic _ = False

compileIntrinsic ::
    String ->
    [AOperand] ->
    LlvmType ->
    IrGen LlvmValue
compileIntrinsic "println" args _ = compilePrintln args
compileIntrinsic "map" args retTy = compileMap args retTy
compileIntrinsic "strcat" args retTy = compileStrcat args retTy
compileIntrinsic "int_to_string" args retTy = compileIntToString args retTy
compileIntrinsic name _ _ = error $ "Unknown intrinsic: " ++ name

compilePrintln ::
    [AOperand] ->
    IrGen LlvmValue
compilePrintln [arg] = do
    compiledArg <- compileOperand arg
    let argType = getValueType compiledArg

    case argType of
        LlvmPointer LlvmI8 -> do
            puts <- useDep putsDependency
            tell [LlvmCallStmt puts LlvmI32 [compiledArg]]
            pure $ LlvmUndef LlvmVoid
        LlvmI32 -> do
            formatStr <- newStrTemplate "%d\\0A"
            printf <- useDep printfDependency
            tell [LlvmCallStmt printf LlvmI32 [formatStr, compiledArg]]
            pure $ LlvmUndef LlvmVoid
        _ -> do
            formatStr <- newStrTemplate "<value>\\0A" -- todo: handle this
            printf <- useDep printfDependency
            tell [LlvmCallStmt printf LlvmI32 [formatStr]]
            pure $ LlvmUndef LlvmVoid
compilePrintln _ = error "println intrinsic expects exactly 1 argument"

compileMap ::
    [AOperand] ->
    LlvmType ->
    IrGen LlvmValue
compileMap [lambda, array] resultTy = do
    compiledArray <- compileOperand array
    modName <- asks moduleName

    let (elemTy, fnRetType) = case resultTy of
            LlvmPointer (LlvmArray _ ty) -> (ty, ty) -- element type is result array element type
            _ -> (LlvmI32, LlvmI32) -- fallback
    let lambdaName = case lambda of
            OpVar name -> name
            _ -> error "map expects a function name as first argument"

    let fnType = LlvmFn fnRetType [elemTy]
    let qualifiedLambdaName = qualifyWithModule modName lambdaName
    let compiledLambda = LlvmGlobal fnType qualifiedLambdaName

    -- todo: extract actual length from array metadata or type info
    let arrayLen = 4

    let newArrayTy = LlvmArray arrayLen fnRetType
    newArrayPtr <- saveTmp (LlvmAlloca newArrayTy Nothing) (LlvmPointer newArrayTy)

    indexPtr <- saveTmp (LlvmAlloca LlvmI32 Nothing) (LlvmPointer LlvmI32)
    tell [LlvmStore (intLiteral 0) indexPtr]

    blockNum <- gets nextRegister
    let condLabel = "map_cond_" ++ show blockNum
    let bodyLabel = "map_body_" ++ show (blockNum + 1)
    let endLabel = "map_end_" ++ show (blockNum + 2)

    tell [LlvmBr condLabel]

    tell [LlvmLabel condLabel]
    currentIndex <- saveTmp (LlvmLoad indexPtr) LlvmI32
    cond <- saveTmp (LlvmICmp LlvmI32 "slt" currentIndex (intLiteral arrayLen)) LlvmI1
    tell [LlvmBrCond cond bodyLabel endLabel]

    tell [LlvmLabel bodyLabel]
    currentIndex2 <- saveTmp (LlvmLoad indexPtr) LlvmI32

    elemPtr <- saveTmp (LlvmGetElementPtr elemTy compiledArray [currentIndex2] True) (LlvmPointer elemTy)
    element <- saveTmp (LlvmLoad elemPtr) elemTy

    mappedElement <- saveTmp (LlvmCall compiledLambda fnRetType [element]) fnRetType

    resultPtr <- saveTmp (LlvmGetElementPtr fnRetType newArrayPtr [currentIndex2] True) (LlvmPointer fnRetType)
    tell [LlvmStore mappedElement resultPtr]

    nextIndex <- saveTmp (LlvmAdd LlvmI32 currentIndex2 (intLiteral 1)) LlvmI32
    tell [LlvmStore nextIndex indexPtr]

    tell [LlvmBr condLabel]
    tell [LlvmLabel endLabel]

    pure newArrayPtr
compileMap _ _ = error "map intrinsic expects exactly 2 arguments (function, array)"

compileStrcat ::
    [AOperand] ->
    LlvmType ->
    IrGen LlvmValue
compileStrcat [s1, s2] _retTy = do
    str1 <- compileOperand s1
    str2 <- compileOperand s2

    strlenFn <- useDep strlenDependency
    len1 <- saveTmp (LlvmCall strlenFn LlvmI64 [str1]) LlvmI64
    len2 <- saveTmp (LlvmCall strlenFn LlvmI64 [str2]) LlvmI64

    totalLen <- saveTmp (LlvmAdd LlvmI64 len1 len2) LlvmI64
    allocSize <- saveTmp (LlvmAdd LlvmI64 totalLen (longLiteral 1)) LlvmI64

    mallocFn <- useDep mallocDependency
    newStr <- saveTmp (LlvmCall mallocFn (LlvmPointer LlvmI8) [allocSize]) (LlvmPointer LlvmI8)

    strcpyFn <- useDep strcpyDependency
    _ <- saveTmp (LlvmCall strcpyFn (LlvmPointer LlvmI8) [newStr, str1]) (LlvmPointer LlvmI8)

    destOffset <- saveTmp (LlvmGetElementPtr LlvmI8 newStr [len1] False) (LlvmPointer LlvmI8)

    _ <- saveTmp (LlvmCall strcpyFn (LlvmPointer LlvmI8) [destOffset, str2]) (LlvmPointer LlvmI8)

    pure newStr
compileStrcat _ _ = error "strcat intrinsic expects exactly 2 arguments"

compileIntToString ::
    [AOperand] ->
    LlvmType ->
    IrGen LlvmValue
compileIntToString [numOp] _retTy = do
    intVal <- compileOperand numOp

    i64Val <- case getValueType intVal of
        LlvmI64 -> pure intVal
        LlvmI32 -> saveTmp (LlvmSExt intVal LlvmI64) LlvmI64
        _ -> saveTmp (LlvmSExt intVal LlvmI64) LlvmI64

    mallocFn <- useDep mallocDependency
    buffer <- saveTmp (LlvmCall mallocFn (LlvmPointer LlvmI8) [longLiteral 21]) (LlvmPointer LlvmI8)

    endPtr <- saveTmp (LlvmGetElementPtr LlvmI8 buffer [longLiteral 20] False) (LlvmPointer LlvmI8)
    tell [LlvmStore (LlvmLiteral LlvmI8 "0") endPtr]

    isNegative <- saveTmp (LlvmICmp LlvmI64 "slt" i64Val (longLiteral 0)) LlvmI1

    negated <- saveTmp (LlvmSub LlvmI64 (longLiteral 0) i64Val) LlvmI64
    workVal <- saveTmp (LlvmSelect isNegative negated i64Val LlvmI64) LlvmI64

    entryLabel <- freshBlockName "int_to_str_entry"
    loopLabel <- freshBlockName "int_to_str_loop"
    loopBodyLabel <- freshBlockName "int_to_str_body"
    afterLoopLabel <- freshBlockName "int_to_str_after"
    addMinusLabel <- freshBlockName "int_to_str_minus"
    doneLabel <- freshBlockName "int_to_str_done"

    nextValReg <- freshNamedReg "next_val" LlvmI64
    nextPosReg <- freshNamedReg "next_pos" LlvmI64

    tell [LlvmBr entryLabel]

    tell [LlvmLabel entryLabel]
    tell [LlvmBr loopLabel]

    tell [LlvmLabel loopLabel]
    currentVal <- saveTmp (LlvmPhi LlvmI64 [(workVal, entryLabel), (nextValReg, loopBodyLabel)]) LlvmI64
    currentPos <- saveTmp (LlvmPhi LlvmI64 [(longLiteral 19, entryLabel), (nextPosReg, loopBodyLabel)]) LlvmI64

    digit <- saveTmp (LlvmSRem LlvmI64 currentVal (longLiteral 10)) LlvmI64
    digitChar <- saveTmp (LlvmAdd LlvmI64 digit (longLiteral 48)) LlvmI64
    digitCharI8 <- saveTmp (LlvmTrunc digitChar LlvmI8) LlvmI8

    writePtr <- saveTmp (LlvmGetElementPtr LlvmI8 buffer [currentPos] False) (LlvmPointer LlvmI8)
    tell [LlvmStore digitCharI8 writePtr]

    _ <- saveToNamedReg nextValReg (LlvmSDiv LlvmI64 currentVal (longLiteral 10))
    _ <- saveToNamedReg nextPosReg (LlvmSub LlvmI64 currentPos (longLiteral 1))

    continueLoop <- saveTmp (LlvmICmp LlvmI64 "sgt" nextValReg (longLiteral 0)) LlvmI1
    tell [LlvmBrCond continueLoop loopBodyLabel afterLoopLabel]

    tell [LlvmLabel loopBodyLabel]
    tell [LlvmBr loopLabel]

    tell [LlvmLabel afterLoopLabel]

    tell [LlvmBrCond isNegative addMinusLabel doneLabel]

    tell [LlvmLabel addMinusLabel]
    minusPos <- saveTmp (LlvmSub LlvmI64 currentPos (longLiteral 1)) LlvmI64
    minusPtr <- saveTmp (LlvmGetElementPtr LlvmI8 buffer [minusPos] False) (LlvmPointer LlvmI8)
    tell [LlvmStore (LlvmLiteral LlvmI8 "45") minusPtr] -- '-' = 45
    tell [LlvmBr doneLabel]

    tell [LlvmLabel doneLabel]
    finalPos <- saveTmp (LlvmPhi LlvmI64 [(currentPos, afterLoopLabel), (minusPos, addMinusLabel)]) LlvmI64
    
    saveTmp (LlvmGetElementPtr LlvmI8 buffer [finalPos] False) (LlvmPointer LlvmI8)
compileIntToString _ _ = error "int_to_string intrinsic expects exactly 1 argument"
