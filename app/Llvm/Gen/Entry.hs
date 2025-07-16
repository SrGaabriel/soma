{-# LANGUAGE LambdaCase #-}
module Llvm.Gen.Entry (compileLlvmModule, runLlvmCodeGen, runLlvmCodeGenAndTranscribe) where
import Llvm.Gen.Core (IrGen, runIrGen, globalDefaultState, globalDefaultEnv)
import Syntax.Tree (Expr (..), exprChildren)
import Llvm.Modules (LlvmModule (..))
import Llvm.Gen.Bindings (compileBindingDef)
import Llvm.Ir (IR(toLlvm))
import Data.Maybe (mapMaybe)
compileLlvmModule :: String -> Expr -> IrGen LlvmModule
compileLlvmModule name root = do
    let topLevelMembers = exprChildren root
    fns <- sequence $ mapMaybe (\case
                binding@(ExprBindingDef {}) -> Just (compileBindingDef binding)
                u -> Nothing
            ) topLevelMembers
    return $ LlvmModule 
        { moduleName = name
        , moduleFunctions = fns
        }

runLlvmCodeGen :: String -> Expr -> LlvmModule
runLlvmCodeGen name root = 
    let ((moduleResult, _collectedStatements), _finalStat) = runIrGen globalDefaultEnv globalDefaultState (compileLlvmModule name root)
    in moduleResult

runLlvmCodeGenAndTranscribe :: String -> Expr -> String
runLlvmCodeGenAndTranscribe name root =
    let moduleResult = runLlvmCodeGen name root
    in toLlvm moduleResult