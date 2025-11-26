{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Llvm.Gen.Operands (compileOperand) where

import Alloy.Ir (
    AConst (CBool, CInt, CString, CUnit),
    AOperand (..),
 )
import Alloy.Naming (qualifyWithModule)
import Control.Monad.Reader (asks)
import Control.Monad.State (gets)
import qualified Data.Map as Map
import Llvm.Gen.Core (
    IrGen,
    IrGenEnv (moduleName, opTypeEnv),
    IrGenState (valueSubst),
    applySubstitutions,
 )
import Llvm.Gen.Templates (newStrTemplate)
import Llvm.Gen.TypeConversion (getConstructorTag)
import Llvm.Types (LlvmType (LlvmAnonymous, LlvmI64, LlvmI8, LlvmPointer))
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
                    let tag = getConstructorTag name (-1)
                    in if tag /= -1
                        then
                            let structTy = LlvmAnonymous [LlvmI8, LlvmI64]
                                valStr = "{ i8 " ++ show tag ++ ", i64 0 }"
                            in pure $ LlvmLiteral structTy valStr
                        else do
                            modName <- asks moduleName
                            let finalName = if name == "main" then name else qualifyWithModule modName name
                            let quotedName = "\"" ++ finalName ++ "\""
                            -- todo: have a proper type here
                            pure $ LlvmGlobal (LlvmPointer LlvmI8) quotedName
compileOperand (OpConst (CInt n)) = pure $ intLiteral n
compileOperand (OpConst (CBool n)) = pure $ boolLiteral n
compileOperand (OpConst (CString str)) = newStrTemplate str
compileOperand (OpConst CUnit) = error "Can't compile void"
