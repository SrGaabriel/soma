module Llvm.Gen.Op where
import Alloy.Ir
import Llvm.Instructions
import Llvm.Gen.Core
import Llvm.Gen.Operands (compileOperand)
import Llvm.Gen.TypeConversion (convertType)

compileOp :: AOp -> IrGen LlvmInstruction
compileOp (OpLoad rOperand) = do
    operand <- compileOperand rOperand
    pure $ LlvmLoad operand
compileOp (OpAllocStack ty) = do
    -- todo: alignment etc etc
    let llvmTy = convertType ty
    pure $ LlvmAlloca llvmTy Nothing
compileOp u = error $ "Unsuported op: " ++ show u