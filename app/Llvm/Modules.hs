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
    , moduleStructs :: [LlvmStruct]
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

data LlvmStruct = LlvmStruct
    { structName :: String
    , structFields :: [LlvmType]
    }
    deriving (Show, Eq)

data LlvmBlock = LlvmBlock
    { blockName :: String
    , blockStatements :: [LlvmStatement]
    }
    deriving (Show)

instance IR LlvmModule where
    toLlvm (LlvmModule _ functions structs dependencies) =
        unlines (map toLlvm $ nub dependencies)
            ++ "\n\n"
            ++ unlines (map toLlvm $ nub structs)
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

instance IR LlvmStruct where
    toLlvm (LlvmStruct name fields) =
        "%"
            ++ name
            ++ " = type {"
            ++ intercalate ", " (map toLlvm fields)
            ++ "}"

instance IR LlvmBlock where
    toLlvm (LlvmBlock name stmts) = name ++ ":\n" ++ unlines (map toLlvm stmts)
