{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Llvm.Gen.Operands where

import Alloy.Ir
import Control.Monad.Reader (asks)
import Control.Monad.State (modify)
import Data.Hashable (hash)
import qualified Data.Map as Map
import Llvm.Dependencies (LinkageType (PrivateLinkage), LlvmDependency (..))
import Llvm.Gen.Core
import Llvm.Instructions (LlvmInstruction (LlvmGetElementPtr))
import Llvm.Types (LlvmType (LlvmArray, LlvmI8, LlvmPointer))
import Llvm.Values

compileOperand :: AOperand -> IrGen LlvmValue
compileOperand (OpVar name) = do
    tEnv <- asks opTypeEnv
    let Just opTy = Map.lookup name tEnv
    pure $ LlvmRegister opTy name
compileOperand (OpConst (CInt n)) = pure $ intLiteral n
compileOperand (OpConst (CBool n)) = pure $ boolLiteral n
compileOperand (OpConst CUnit) = error "Can't compile void"
compileOperand (OpConst (CString str)) = do
    let dpName = "str_" ++ show (hash str)
    let depType = LlvmArray (length str + 1) LlvmI8
    let dependency =
            LlvmConstantDependency
                { constantName = dpName
                , constantValue = LlvmLiteral depType ("c\"" ++ str ++ "\00\"")
                , constantLinkage = Just PrivateLinkage
                }
    modify $ \s -> s{irDependencies = dependency : irDependencies s}

    let ptrInstr = LlvmGetElementPtr depType (LlvmGlobal depType dpName) [intLiteral 0, intLiteral 0] True
    saveTmp ptrInstr (LlvmPointer LlvmI8)
