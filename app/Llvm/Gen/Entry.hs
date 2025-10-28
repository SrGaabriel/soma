{-# LANGUAGE LambdaCase #-}

module Llvm.Gen.Entry (compileLlvmModule, runLlvmCodeGen, runLlvmCodeGenAndTranscribe) where

import Data.Maybe (mapMaybe)
import Inference.Core (TypeMap)
import Llvm.Gen.Bindings (compileBindingDef)
import Llvm.Gen.Core (IrGen, IrGenState (irDependencies, irFunctions, irStructs), cleanGlobalState, namedDefaultEnv, runIrGen)
import Llvm.Gen.DataTypes (compileDataTypeDef)
import Llvm.Gen.TypeClasses (compileInstanceDef, compileTypeClassDef)
import Llvm.Ir (IR (toLlvm))
import Llvm.Modules (LlvmModule (..))
import Syntax.Tree (Expr (..), exprChildren)

compileLlvmModule :: String -> Expr -> IrGen ()
compileLlvmModule _ root = do
    let topLevelMembers = exprChildren root
    sequence_
        $ mapMaybe
            ( \case
                binding@(ExprBindingDef{}) -> Just (compileBindingDef binding)
                datatype@(ExprDataTypeDef{}) -> Just (compileDataTypeDef datatype)
                typeclass@(ExprTypeClassDef{}) -> Just (compileTypeClassDef typeclass)
                instanc@(ExprInstanceDef{}) -> Just (compileInstanceDef instanc)
                _ -> Nothing
            )
            topLevelMembers

runLlvmCodeGen :: String -> Expr -> TypeMap -> LlvmModule
runLlvmCodeGen name root typeMap =
    let ((_, _collectedStatements), finalStat) = runIrGen (namedDefaultEnv name) (cleanGlobalState typeMap) (compileLlvmModule name root)
        fns = irFunctions finalStat
        structs = irStructs finalStat
        deps = irDependencies finalStat
    in LlvmModule name fns structs deps

runLlvmCodeGenAndTranscribe :: String -> Expr -> TypeMap -> String
runLlvmCodeGenAndTranscribe name root typeMap =
    let moduleResult = runLlvmCodeGen name root typeMap
    in toLlvm moduleResult
