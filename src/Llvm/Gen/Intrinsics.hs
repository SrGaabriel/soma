{-# LANGUAGE FlexibleContexts #-}

module Llvm.Gen.Intrinsics (
    compileIntrinsic,
    isIntrinsic,
) where

import Alloy.Ir (AOperand (..))
import Control.Monad.State (gets)
import Control.Monad.Writer.Class (tell)
import Llvm.Dependencies (LlvmDependency (..))
import Llvm.Gen.Core (IrGen, IrGenState (..), addDependency, saveTmp)
import Llvm.Gen.Operands (compileOperand)
import Llvm.Gen.Templates (newStrTemplate)
import Llvm.Instructions (LlvmInstruction (..), LlvmStatement (..))
import Llvm.Types (LlvmType (..))
import Llvm.Values (LlvmValue (..), getValueType, intLiteral)

isIntrinsic :: String -> Bool
isIntrinsic "println" = True
isIntrinsic "map" = True
isIntrinsic "for" = True
isIntrinsic _ = False

compileIntrinsic ::
    String ->
    [AOperand] ->
    LlvmType ->
    IrGen LlvmValue
compileIntrinsic "println" args _ = compilePrintln args
compileIntrinsic "map" args retTy = compileMap args retTy
compileIntrinsic name _ _ = error $ "Unknown intrinsic: " ++ name

compilePrintln ::
    [AOperand] ->
    IrGen LlvmValue
compilePrintln [arg] = do
    compiledArg <- compileOperand arg
    let argType = getValueType compiledArg

    case argType of
        LlvmPointer LlvmI8 -> do
            addDependency putsDependency
            tell [LlvmCallStmt (LlvmGlobal putsFnType "puts") LlvmI32 [compiledArg]]
            pure $ LlvmUndef LlvmVoid
        LlvmI32 -> do
            formatStr <- newStrTemplate "%d\\0A"
            addDependency printfDependency
            tell [LlvmCallStmt (LlvmGlobal printfFnType "printf") LlvmI32 [formatStr, compiledArg]]
            pure $ LlvmUndef LlvmVoid
        _ -> do
            formatStr <- newStrTemplate "<value>\\0A"
            addDependency printfDependency
            tell [LlvmCallStmt (LlvmGlobal printfFnType "printf") LlvmI32 [formatStr]]
            pure $ LlvmUndef LlvmVoid
compilePrintln _ = error "println intrinsic expects exactly 1 argument"

compileMap ::
    [AOperand] ->
    LlvmType ->
    IrGen LlvmValue
compileMap [lambda, array] resultTy = do
    compiledArray <- compileOperand array

    let (elemTy, fnRetType) = case resultTy of
            LlvmPointer (LlvmArray _ ty) -> (ty, ty) -- element type is result array element type
            _ -> (LlvmI32, LlvmI32) -- fallback
    let lambdaName = case lambda of
            OpVar name -> name
            _ -> error "map expects a function name as first argument"

    let fnType = LlvmFn fnRetType [elemTy]
    let compiledLambda = LlvmGlobal fnType lambdaName

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

-- External function dependencies
putsDependency :: LlvmDependency
putsDependency =
    LlvmFunctionDependency
        { depName = "puts"
        , depReturnType = LlvmI32
        , depParams = [LlvmPointer LlvmI8]
        }

printfDependency :: LlvmDependency
printfDependency =
    LlvmFunctionDependency
        { depName = "printf"
        , depReturnType = LlvmI32
        , depParams = [LlvmPointer LlvmI8, LlvmVararg]
        }

putsFnType :: LlvmType
putsFnType = LlvmFn LlvmI32 [LlvmPointer LlvmI8]

printfFnType :: LlvmType
printfFnType = LlvmFn LlvmI32 [LlvmPointer LlvmI8, LlvmVararg]
