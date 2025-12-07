{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

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
import Control.Monad (forM)
import Control.Monad.Reader (MonadReader (local))
import Control.Monad.State (modify)
import Control.Monad.Writer (listen)
import Data.Bifunctor (bimap)
import Llvm.Gen.Attributes (FunctionAttrs (..), analyzeFunctionAttrs)
import Llvm.Gen.Core (IrGen, IrGenEnv (opTypeEnv), IrGenState (irFunctions), setGraphFunctionContext, setTailCallContext)
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
import Project.Name (Name (..), nameOriginal, nameToLLVM, nameToString)

compileFunction :: AlloyFunction -> IrGen ()
compileFunction aFn@AlloyFunction{afName, afParams, afBlocks, afReturnType} = do
    let name =
            if nameOriginal afName == "main"
                then "soma_main" -- Renamed so C runtime's main() can wrap it
                else nameToLLVM afName
    let opEnv = buildOperandTypeEnv aFn
    -- Detect if this is a graph function (has net, tm, arg params)
    let isGraphFn = case afParams of
            ((n1, _) : (n2, _) : _) | nameToString n1 == "net" && nameToString n2 == "tm" -> True
            _ -> False
    let newEnvFn = local (\env -> env{opTypeEnv = opEnv})
    blocks <- mapM (newEnvFn . setGraphFunctionContext isGraphFn . compileBlock) afBlocks
    let params = map (bimap nameToString convertType) afParams
    let retType = convertType afReturnType
    let provenAttrs = analyzeFunctionAttrs aFn
    let attrs = buildLlvmAttrs isGraphFn provenAttrs
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

{- | Build LLVM function attributes from proven analysis attributes

For graph functions, we're conservative since they interact with the
parallel runtime. For regular functions, we use the proven attributes.
-}
buildLlvmAttrs :: Bool -> FunctionAttrs -> [LlvmFnAttr]
buildLlvmAttrs isGraphFn FunctionAttrs{..}
    | isGraphFn =
        -- Graph functions interact with the parallel runtime, so we're conservative.
        -- Only nounwind is safe since Soma doesn't have exceptions.
        [FnAttrNoUnwind | attrNoUnwind]
    | otherwise =
        -- Regular functions use all proven attributes
        concat
            [ [FnAttrNoUnwind | attrNoUnwind]
            , [FnAttrNoSync | attrNoSync]
            , [FnAttrNoFree | attrNoFree]
            , [FnAttrMemory MemNone | attrMemoryNone]
            , [FnAttrWillReturn | attrWillReturn]
            , [FnAttrNoRecurse | attrNoRecurse]
            ]

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
                { blockName = nameToString (abName aBlock)
                , blockStatements = stmts
                }
    pure block

{- | Detect if the block ends with a tail call pattern:
Last instruction is ILet x _ (OpCall ...) and terminator is ARet (Just (OpVar x))
-}
detectTailCall :: [AInstr] -> ATerminator -> Maybe Name
detectTailCall instrs (ARet (Just (OpVar retName))) =
    case reverse instrs of
        (ILet letName _ (OpCall _ _)) : _
            | letName == retName -> Just letName
        _ -> Nothing
detectTailCall _ _ = Nothing

-- | Check if an instruction is the tail call we detected
isTailCallOp :: Name -> AInstr -> Bool
isTailCallOp tcName (ILet letName _ (OpCall _ _)) = letName == tcName
isTailCallOp _ _ = False
