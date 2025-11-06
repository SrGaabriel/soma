module Llvm.Gen.Instr where

import Alloy.Ir
import Control.Monad.Writer.Class (MonadWriter (tell))
import Llvm.Gen.Core
import Llvm.Gen.Op (compileOp)
import Llvm.Gen.Operands (compileOperand)
import Llvm.Gen.TypeConversion (convertType)
import Llvm.Instructions
import Llvm.Types (deref)
import Llvm.Values (getValueType)

compileInstr :: AInstr -> IrGen ()
compileInstr (ILet letName letTy letOp) = do
    let llTy = convertType letTy
    let reg = mkReg letName llTy
    op <- compileOp letOp llTy
    _ <- saveToReg reg op
    pure ()
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
