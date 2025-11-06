module Llvm.Modules where

import Data.List (intercalate, nub)
import Llvm.Dependencies (LlvmDependency)
import Llvm.Instructions (LlvmStatement)
import Llvm.Ir (IR (toLlvm))
import Llvm.Types (LlvmType)

data LlvmModule = LlvmModule
    { moduleName :: String
    , moduleFunctions :: [LlvmFunction]
    , moduleDependencies :: [LlvmDependency]
    }
    deriving (Show)

data LlvmFunction = LlvmFunction
    { functionName :: String
    , functionParams :: [(String, LlvmType)]
    , functionReturnType :: LlvmType
    , functionBlocks :: [LlvmBlock]
    }
    deriving (Show)

data LlvmBlock = LlvmBlock
    { blockName :: String
    , blockStatements :: [LlvmStatement]
    }
    deriving (Show)

instance IR LlvmModule where
    toLlvm (LlvmModule _ functions dependencies) =
        unlines (map toLlvm $ nub dependencies)
            ++ "\n\n"
            ++ unlines (map toLlvm functions)

instance IR LlvmFunction where
    toLlvm (LlvmFunction name params retType blocks) =
        "define "
            ++ toLlvm retType
            ++ " @"
            ++ name
            ++ "("
            ++ intercalate "," (map (\(n, t) -> toLlvm t ++ " %" ++ n) params)
            ++ ") {\n"
            ++ unlines (map toLlvm blocks)
            ++ "}"

instance IR LlvmBlock where
    toLlvm (LlvmBlock name stmts) = name ++ ":\n" ++ unlines (map toLlvm stmts)
