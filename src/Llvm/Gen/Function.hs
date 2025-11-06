{-# LANGUAGE NamedFieldPuns #-}
module Llvm.Gen.Function where

import Alloy.Ir
import Llvm.Gen.Core (IrGen, IrGenState (irFunctions), IrGenEnv (opTypeEnv))
import Llvm.Modules
import Llvm.Gen.Instr (compileInstr)
import Llvm.Gen.TypeConversion (convertType)
import Data.Bifunctor (Bifunctor(second))
import Control.Monad.State (modify)
import Control.Monad.Writer (listen)
import Control.Monad.Reader (MonadReader (local))
import Llvm.Gen.OperandPass (buildOperandTypeEnv)

compileFunction :: AlloyFunction -> IrGen ()
compileFunction aFn@AlloyFunction{afName, afParams, afBlocks, afReturnType} = do
    let opEnv = buildOperandTypeEnv aFn
    let newEnvFn = local (\env -> env{opTypeEnv=opEnv})
    blocks <- mapM (newEnvFn . compileBlock) afBlocks
    let params = map (second convertType) afParams
    let retType = convertType afReturnType
    let fn =
            LlvmFunction
                { functionName = afName
                , functionBlocks = blocks
                , functionReturnType = retType
                , functionParams = params
                }
    modify (\s -> s{irFunctions = fn : irFunctions s})
    pure ()

compileBlock :: ABlock -> IrGen LlvmBlock
compileBlock aBlock = do
    instrsWithStmts <- mapM (listen . compileInstr) (abInstrs aBlock)
    let stmts = concatMap snd instrsWithStmts
    let block =
            LlvmBlock
                { blockName = abName aBlock
                , blockStatements = stmts
                }
    pure block