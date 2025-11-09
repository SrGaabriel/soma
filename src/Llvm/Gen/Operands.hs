{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Llvm.Gen.Operands (compileOperand) where

import Alloy.Ir (
    AConst (CBool, CInt, CString, CUnit),
    AOperand (..),
 )
import Control.Monad.Reader (asks)
import Control.Monad.State (gets)
import qualified Data.Map as Map
import Llvm.Gen.Core (
    IrGen,
    IrGenEnv (opTypeEnv),
    IrGenState (valueSubst),
    applySubstitutions,
 )
import Llvm.Gen.Templates (newStrTemplate)
import Llvm.Types (LlvmType (LlvmI8, LlvmPointer))
import Llvm.Values (
    LlvmValue (LlvmGlobal, LlvmRegister),
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
compileOperand (OpConst (CString str)) = newStrTemplate str
compileOperand (OpConst CUnit) = error "Can't compile void"
