module Llvm.Gen.Instr (
    compileInstr,
    compileTerminator,
) where

import Alloy.Ir
import Control.Monad.Writer.Class (MonadWriter (tell))
import Llvm.Gen.Core
import Llvm.Gen.Op (compileOp)
import Llvm.Gen.Operands (compileOperand)
import Llvm.Gen.TypeConversion (convertType)
import Llvm.Instructions
import Llvm.Types (LlvmType (..), deref)
import Llvm.Values (LlvmValue (..), getValueType)

compileInstr :: AInstr -> IrGen ()
compileInstr (ILet letName letTy letOp) = do
    let llTy = convertType letTy
    resultVal <- compileOp letOp llTy
    recordSubstitution letName resultVal
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
compileInstr (IEffect (EffDrop _value)) =
    pure ()

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
    tell [LlvmBr target]
compileTerminator (ACondBr cond trueBlock _trueArgs falseBlock _falseArgs) = do
    llvmCond <- compileOperand cond
    -- todo: handle block arguments
    tell [LlvmBrCond llvmCond trueBlock falseBlock]
compileTerminator (ASwitch scrutinee cases maybeDefault) = do
    llvmScrutinee <- compileOperand scrutinee
    let scrutineeTy = getValueType llvmScrutinee
    let llvmCases = [(LlvmLiteral scrutineeTy (show tag), label) | (tag, label) <- cases]

    let defaultLabel = case maybeDefault of
            Just lbl -> lbl
            Nothing -> case cases of
                (_, lbl) : _ -> lbl
                [] -> "unreachable_default"

    tell [LlvmSwitch llvmScrutinee defaultLabel llvmCases]
compileTerminator AUnreachable = do
    tell [LlvmUnreachable]
