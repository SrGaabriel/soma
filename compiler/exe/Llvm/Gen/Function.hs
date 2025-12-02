{-# LANGUAGE NamedFieldPuns #-}

module Llvm.Gen.Function where

import Alloy.Ir (
    ABlock (abInstrs, abName, abTerminator),
    AInstr (..),
    AOp (..),
    AOperand (..),
    ATerminator (..),
    AlloyFunction (
        AlloyFunction,
        afBlocks,
        afName,
        afParams,
        afReturnType
    ),
 )
import Alloy.Naming (qualifyWithModule)
import Control.Monad (forM)
import Control.Monad.Reader (MonadReader (local), asks)
import Control.Monad.State (modify)
import Control.Monad.Writer (listen)
import Data.Bifunctor (Bifunctor (second))
import Llvm.Gen.Core (IrGen, IrGenEnv (moduleName, opTypeEnv), IrGenState (irFunctions), setGraphFunctionContext, setTailCallContext)
import Llvm.Gen.Instr (compileInstr, compileTerminator)
import Llvm.Gen.OperandPass (buildOperandTypeEnv)
import Llvm.Gen.TypeConversion (convertType)
import Llvm.Modules (
    LlvmBlock (..),
    LlvmFunction (
        LlvmFunction,
        functionAttributes,
        functionBlocks,
        functionName,
        functionParams,
        functionReturnType
    ),
 )
import Llvm.Types (LlvmFnAttr (..), LlvmMemoryEffect (..))

compileFunction :: AlloyFunction -> IrGen ()
compileFunction aFn@AlloyFunction{afName, afParams, afBlocks, afReturnType} = do
    name <-
        if afName == "main"
            then pure "soma_main" -- Renamed so C runtime's main() can wrap it
            else do
                modName <- asks moduleName
                pure $ qualifyWithModule modName afName
    let opEnv = buildOperandTypeEnv aFn
    -- Detect if this is a graph function (has net, tm, arg params)
    let isGraphFn = case afParams of
            (("net", _) : ("tm", _) : _) -> True
            _ -> False
    let newEnvFn = local (\env -> env{opTypeEnv = opEnv})
    blocks <- mapM (newEnvFn . setGraphFunctionContext isGraphFn . compileBlock) afBlocks
    let params = map (second convertType) afParams
    let retType = convertType afReturnType
    -- TODO: adjust function attributes based on analysis
    let attrs = if isGraphFn
            then [FnAttrNoUnwind]
            else [FnAttrNoUnwind, FnAttrNoSync, FnAttrNoFree, FnAttrMemory MemNone, FnAttrReadNone, FnAttrWillReturn]
    let fn =
            LlvmFunction
                { functionName = "\"" ++ name ++ "\""
                , functionBlocks = blocks
                , functionReturnType = retType
                , functionParams = params
                , functionAttributes = attrs
                }
    modify (\s -> s{irFunctions = fn : irFunctions s})
    pure ()

compileBlock :: ABlock -> IrGen LlvmBlock
compileBlock aBlock = do
    -- Detect tail call pattern: last instruction is a call whose result is immediately returned
    let instrs = abInstrs aBlock
        terminator = abTerminator aBlock
        tailCallName = detectTailCall instrs terminator

    -- Compile instructions, marking the tail call if detected
    instrsWithStmts <- case tailCallName of
        Nothing -> mapM (listen . compileInstr) instrs
        Just tcName ->
            -- Compile all instructions, but mark the tail call instruction
            forM (zip [0 ..] instrs) $ \(idx, instr) -> do
                let isLastInstr = idx == length instrs - 1
                    isTailCallInstr = isLastInstr && isTailCallOp tcName instr
                if isTailCallInstr
                    then listen $ setTailCallContext True $ compileInstr instr
                    else listen $ compileInstr instr
    let instrStmts = concatMap snd instrsWithStmts

    (_, termStmts) <- listen $ compileTerminator terminator

    let stmts = instrStmts ++ termStmts
    let block =
            LlvmBlock
                { blockName = abName aBlock
                , blockStatements = stmts
                }
    pure block

{- | Detect if the block ends with a tail call pattern:
Last instruction is ILet x _ (OpCall ...) and terminator is ARet (Just (OpVar x))
-}
detectTailCall :: [AInstr] -> ATerminator -> Maybe String
detectTailCall instrs (ARet (Just (OpVar retName))) =
    case reverse instrs of
        (ILet letName _ (OpCall _ _)) : _
            | letName == retName -> Just letName
        _ -> Nothing
detectTailCall _ _ = Nothing

-- | Check if an instruction is the tail call we detected
isTailCallOp :: String -> AInstr -> Bool
isTailCallOp tcName (ILet letName _ (OpCall _ _)) = letName == tcName
isTailCallOp _ _ = False
