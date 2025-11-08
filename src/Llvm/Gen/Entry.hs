{-# LANGUAGE NamedFieldPuns #-}

module Llvm.Gen.Entry (
    compileLlvmModule,
    runLlvmCodeGen,
    runLlvmCodeGenAndTranscribe,
) where

import Alloy.Ir (AlloyModule (AlloyModule, amFunctions, amName))
import Llvm.Gen.Core (IrGen, globalDefaultState, irDependencies, irFunctions, namedDefaultEnv, runIrGen)
import Llvm.Gen.Function (compileFunction)
import Llvm.Ir (IR (toLlvm))
import Llvm.Modules (LlvmModule (..))

compileLlvmModule :: AlloyModule -> IrGen ()
compileLlvmModule AlloyModule{amFunctions} = do
    mapM_ compileFunction amFunctions

runLlvmCodeGen :: AlloyModule -> LlvmModule
runLlvmCodeGen alloyModule =
    let name = amName alloyModule
        env = namedDefaultEnv name
        ((_, _collectedStatements), finalStat) =
            runIrGen env globalDefaultState (compileLlvmModule alloyModule)
        fns = irFunctions finalStat
        deps = irDependencies finalStat
    in LlvmModule name fns deps

runLlvmCodeGenAndTranscribe :: AlloyModule -> String
runLlvmCodeGenAndTranscribe alloy =
    let moduleResult = runLlvmCodeGen alloy
    in toLlvm moduleResult
