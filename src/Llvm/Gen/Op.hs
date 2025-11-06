module Llvm.Gen.Op where

import Alloy.Ir
import Llvm.Gen.Core
import Llvm.Gen.Operands (compileOperand)
import Llvm.Gen.TypeConversion (convertType)
import Llvm.Instructions
import Llvm.Types (LlvmType (..), deref)
import Llvm.Values (LlvmValue (..), getValueType)

compileOp :: AOp -> LlvmType -> IrGen LlvmInstruction
compileOp (OpLoad rOperand) _ = do
    operand <- compileOperand rOperand
    pure $ LlvmLoad operand
compileOp (OpAllocStack ty) _ = do
    let llvmTy = convertType ty
    pure $ LlvmAlloca llvmTy Nothing
compileOp (OpBin k a b) _ = do
    lhs <- compileOperand a
    rhs <- compileOperand b
    let ty = getValueType lhs
    pure $ case k of
        IAdd -> LlvmAdd ty lhs rhs
        ISub -> LlvmSub ty lhs rhs
        IMul -> LlvmMul ty lhs rhs
        other -> error $ "Unsupported binary op in LLVM codegen: " ++ show other
compileOp (OpUnary k a) _ = do
    v <- compileOperand a
    let ty = getValueType v
    case k of
        Neg ->
            let zero = LlvmLiteral ty "0"
            in pure $ LlvmSub ty zero v
        Not ->
            if ty == LlvmI1
                then pure $ LlvmICmp ty "eq" v (LlvmLiteral LlvmI1 "0")
                else error "Bitwise NOT for non-boolean not supported in LLVM codegen yet"
compileOp (OpCmp c a b) _ = do
    lhs <- compileOperand a
    rhs <- compileOperand b
    let ty = getValueType lhs
    pure $ LlvmICmp ty (cmpOpToLlvm c) lhs rhs
compileOp (OpIndex base idx) _ = do
    b <- compileOperand base
    i <- compileOperand idx
    let elemTy = deref (getValueType b)
    pure $ LlvmGetElementPtr elemTy b [i] True
compileOp (OpProject agg ix) _ = do
    av <- compileOperand agg
    let aggTy = getValueType av
    pure $ LlvmExtractValue aggTy av ix
compileOp (OpCall callable aArgs) opType = do
    args <- mapM compileOperand aArgs
    fn <- case callable of
        Direct fnName -> pure $ LlvmGlobal opType fnName
        Indirect operand -> compileOperand operand

    pure $ LlvmCall fn opType args
compileOp (OpConstruct _cName _cTag _cFields) _ =
    pure LlvmTodoInstruction
compileOp (OpMakeArray _xs) _ =
    pure LlvmTodoInstruction
compileOp (OpMakeTuple _xs) _ =
    pure LlvmTodoInstruction
compileOp _ _ = undefined

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
