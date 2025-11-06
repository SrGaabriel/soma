module Llvm.Gen.Instr where

import Alloy.Ir
import Llvm.Gen.Core
import Llvm.Gen.TypeConversion (convertType)
import Llvm.Gen.Op (compileOp)
import Llvm.Gen.Operands (compileOperand)
import Llvm.Instructions (LlvmStatement(LlvmStore))
import Control.Monad.Writer.Class (MonadWriter(tell))

compileInstr :: AInstr -> IrGen ()
compileInstr (ILet letName letTy letOp) = do
    let llTy = convertType letTy
    let reg = mkReg letName llTy
    op <- compileOp letOp
    _ <- saveToReg reg op
    pure ()
compileInstr (IEffect (EffStore value addr)) = do
    llValue <- compileOperand value
    llAddr <- compileOperand addr
    tell [LlvmStore llValue llAddr]
compileInstr (IEffect (EffStoreIndex array index value)) = do
    undefined
compileInstr (IEffect (EffDrop value)) = do
    undefined