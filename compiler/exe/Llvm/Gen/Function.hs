{-# LANGUAGE NamedFieldPuns #-}

module Llvm.Gen.Function where

import Alloy.Ir (
    ABlock (abInstrs, abName, abTerminator),
    AlloyFunction (
        AlloyFunction,
        afBlocks,
        afName,
        afParams,
        afReturnType
    ),
 )
import Alloy.Naming (qualifyWithModule)
import Control.Monad.Reader (MonadReader (local), asks)
import Control.Monad.State (modify)
import Control.Monad.Writer (listen)
import Data.Bifunctor (Bifunctor (second))
import Llvm.Gen.Core (IrGen, IrGenEnv (moduleName, opTypeEnv), IrGenState (irFunctions))
import Llvm.Gen.Instr (compileInstr, compileTerminator)
import Llvm.Gen.OperandPass (buildOperandTypeEnv)
import Llvm.Gen.TypeConversion (convertType)
import Llvm.Modules (
    LlvmBlock (..),
    LlvmFunction (
        LlvmFunction,
        functionBlocks,
        functionName,
        functionParams,
        functionReturnType
    ),
 )

compileFunction :: AlloyFunction -> IrGen ()
compileFunction aFn@AlloyFunction{afName, afParams, afBlocks, afReturnType} = do
    name <-
        if afName == "main"
            then pure afName
            else do
                modName <- asks moduleName
                pure $ qualifyWithModule modName afName
    let opEnv = buildOperandTypeEnv aFn
    let newEnvFn = local (\env -> env{opTypeEnv = opEnv})
    blocks <- mapM (newEnvFn . compileBlock) afBlocks
    let params = map (second convertType) afParams
    let retType = convertType afReturnType
    let fn =
            LlvmFunction
                { functionName = "\"" ++ name ++ "\""
                , functionBlocks = blocks
                , functionReturnType = retType
                , functionParams = params
                }
    modify (\s -> s{irFunctions = fn : irFunctions s})
    pure ()

compileBlock :: ABlock -> IrGen LlvmBlock
compileBlock aBlock = do
    instrsWithStmts <- mapM (listen . compileInstr) (abInstrs aBlock)
    let instrStmts = concatMap snd instrsWithStmts

    (_, termStmts) <- listen $ compileTerminator (abTerminator aBlock)

    let stmts = instrStmts ++ termStmts
    let block =
            LlvmBlock
                { blockName = abName aBlock
                , blockStatements = stmts
                }
    pure block
