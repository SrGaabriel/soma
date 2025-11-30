{-# LANGUAGE NamedFieldPuns #-}

module Llvm.Gen.Entry (
    compileLlvmModule,
    runLlvmCodeGen,
    runLlvmCodeGenAndTranscribe,
) where

import Alloy.Ir (AlloyFunction (..), AlloyModule (AlloyModule, amDictionaries, amFunctions, amName))
import Llvm.Gen.CRuntime (cRuntimeExternalDeclarations)
import Llvm.Gen.Core (IrGen, IrGenEnv (..), globalDefaultState, irDependencies, irFunctions, namedDefaultEnv, runIrGen)
import Llvm.Gen.Dictionary (compileDictionaries)
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
runLlvmCodeGen alloyModule@AlloyModule{amName = name, amDictionaries = dicts, amFunctions = allFunctions} =
    let
        (_typeStructDecls, dictGlobals, dictLookupMap) = compileDictionaries name dicts allFunctions

        env = (namedDefaultEnv name){dictMap = dictLookupMap}

        ((_, _collectedStatements), finalStat) =
            runIrGen env globalDefaultState (compileLlvmModule alloyModule)
        fns = irFunctions finalStat
        deps = irDependencies finalStat
    in
        LlvmModule name fns deps dictGlobals

runLlvmCodeGenAndTranscribe :: AlloyModule -> String
runLlvmCodeGenAndTranscribe alloy@AlloyModule{amDictionaries = dicts, amFunctions = allFunctions} =
    let moduleResult = runLlvmCodeGen alloy
        baseIR = toLlvm moduleResult

        (typeStructDecls, _dictGlobals, _dictMap) = compileDictionaries (amName alloy) dicts allFunctions
        structDeclarations = unlines typeStructDecls
    in cRuntimeExternalDeclarations ++ structDeclarations ++ "\n" ++ baseIR
