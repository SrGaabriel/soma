{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Llvm.Gen.Operands (compileOperand) where

import Alloy.Ir (
    AConst (CBool, CInt, CString, CUnit),
    AOperand (..),
 )
import Control.Monad.Reader (asks)
import Control.Monad.State (gets, modify)
import Data.Hashable (hash)
import qualified Data.Map as Map
import Llvm.Dependencies (LinkageType (PrivateLinkage), LlvmDependency (..))
import Llvm.Gen.Core (
    IrGen,
    IrGenEnv (opTypeEnv),
    IrGenState (irDependencies, valueSubst),
    applySubstitutions,
    saveTmp,
 )
import Llvm.Instructions (LlvmInstruction (LlvmGetElementPtr))
import Llvm.Types (LlvmType (LlvmArray, LlvmI8, LlvmPointer))
import Llvm.Values (
    LlvmValue (LlvmGlobal, LlvmLiteral, LlvmRegister),
    boolLiteral,
    intLiteral,
 )

compileOperand :: AOperand -> IrGen LlvmValue
compileOperand (OpVar name) = do
    tEnv <- asks opTypeEnv
    case Map.lookup name tEnv of
        Just opTy -> do
            let reg = LlvmRegister opTy name
            applySubstitutions reg
        Nothing -> do
            st <- gets valueSubst
            case Map.lookup name st of
                Just val -> pure val
                Nothing ->
                    -- todo: have a proper type here
                    pure $ LlvmGlobal (LlvmPointer LlvmI8) name
compileOperand (OpConst (CInt n)) = pure $ intLiteral n
compileOperand (OpConst (CBool n)) = pure $ boolLiteral n
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
compileOperand (OpConst CUnit) = error "Can't compile void"
