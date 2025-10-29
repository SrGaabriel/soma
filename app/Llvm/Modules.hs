module Llvm.Modules where

import Data.List (intercalate, nub)
import Data.Map (Map)
import qualified Data.Map as Map
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
    , functionParams :: Map String LlvmType
    , functionReturnType :: LlvmType
    , functionBlocks :: [LlvmBlock]
    , functionStatements :: [LlvmStatement]
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
    toLlvm (LlvmFunction name params retType blocks stmts) =
        "define "
            ++ toLlvm retType
            ++ " @"
            ++ name
            ++ "("
            ++ intercalate "," (map (\(n, t) -> toLlvm t ++ " %" ++ n) (Map.toList params))
            ++ ") {\n"
            ++ unlines (map toLlvm blocks)
            ++ unlines (map toLlvm stmts)
            ++ "}"

instance IR LlvmBlock where
    toLlvm (LlvmBlock name stmts) = name ++ ":\n" ++ unlines (map toLlvm stmts)
