module Llvm.Modules where

import Data.List (intercalate, nub)
import Llvm.Dependencies (LlvmDependency)
import Llvm.Instructions (LlvmStatement)
import Llvm.Ir (IR (toLlvm))
import Llvm.Types (LlvmType, LlvmFnAttr, fnAttrToLlvm)

data LlvmModule = LlvmModule
    { moduleName :: String
    , moduleFunctions :: [LlvmFunction]
    , moduleDependencies :: [LlvmDependency]
    , moduleGlobals :: [LlvmGlobal]
    }
    deriving (Show)

data LlvmGlobal = LlvmGlobal
    { globalName :: String
    , globalType :: LlvmType
    , globalConstant :: Bool
    , globalInitializer :: String
    , globalLinkage :: String
    }
    deriving (Show)

data LlvmFunction = LlvmFunction
    { functionName :: String
    , functionParams :: [(String, LlvmType)]
    , functionReturnType :: LlvmType
    , functionBlocks :: [LlvmBlock]
    , functionAttributes :: [LlvmFnAttr]
    }
    deriving (Show)

data LlvmBlock = LlvmBlock
    { blockName :: String
    , blockStatements :: [LlvmStatement]
    }
    deriving (Show)

instance IR LlvmModule where
    toLlvm (LlvmModule _ functions dependencies globals) =
        unlines (map toLlvm $ nub dependencies)
            ++ "\n\n"
            ++ unlines (map toLlvm globals)
            ++ "\n\n"
            ++ unlines (map toLlvm functions)

instance IR LlvmGlobal where
    toLlvm (LlvmGlobal name ty isConst initializer linkage) =
        "@"
            ++ name
            ++ " = "
            ++ linkage
            ++ " "
            ++ (if isConst then "constant " else "global ")
            ++ toLlvm ty
            ++ " "
            ++ initializer

instance IR LlvmFunction where
    toLlvm (LlvmFunction name params retType blocks attrs) =
        "define "
            ++ toLlvm retType
            ++ " @"
            ++ name
            ++ "("
            ++ intercalate "," (map (\(n, t) -> toLlvm t ++ " %" ++ n) params)
            ++ ")"
            ++ (if null attrs then "" else " " ++ unwords (map fnAttrToLlvm attrs))
            ++ " {\n"
            ++ unlines (map toLlvm blocks)
            ++ "}"

instance IR LlvmBlock where
    toLlvm (LlvmBlock name stmts) = name ++ ":\n" ++ unlines (map toLlvm stmts)
