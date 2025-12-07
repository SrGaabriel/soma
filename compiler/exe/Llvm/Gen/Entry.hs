{-# LANGUAGE NamedFieldPuns #-}

module Llvm.Gen.Entry (
    compileLlvmModule,
    runLlvmCodeGen,
    runLlvmCodeGenAndTranscribe,
) where

import Alloy.Ir (AlloyFunction (..), AlloyModule (AlloyModule, amFunctions, amName))
import Llvm.Gen.Core (IrGen, globalDefaultState, irDependencies, irFunctions, namedDefaultEnv, runIrGen)
import Llvm.Gen.Function (compileFunction)
import Llvm.Ir (IR (toLlvm))
import Llvm.Modules (LlvmModule (..))

compileLlvmModule :: AlloyModule -> IrGen ()
compileLlvmModule AlloyModule{amFunctions} = do
    -- Only compile concrete monomorphized functions to LLVM
    let concreteFunctions = filter isConcreteFunction amFunctions
    mapM_ compileFunction concreteFunctions
  where
    isConcreteFunction :: AlloyFunction -> Bool
    isConcreteFunction AlloyFunction{afConstraints = constraints} = null constraints

runLlvmCodeGen :: AlloyModule -> LlvmModule
runLlvmCodeGen alloyModule@AlloyModule{amName = name} =
    let
        env = namedDefaultEnv name

        ((_, _collectedStatements), finalStat) =
            runIrGen env globalDefaultState (compileLlvmModule alloyModule)
        fns = irFunctions finalStat
        deps = irDependencies finalStat
    in
        LlvmModule name fns deps []

runLlvmCodeGenAndTranscribe :: AlloyModule -> String
runLlvmCodeGenAndTranscribe alloy =
    let moduleResult = runLlvmCodeGen alloy
        baseIR = toLlvm moduleResult
    in baseIR
