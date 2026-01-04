module Llvm.Modules where

import Data.List (intercalate, nub)
import Llvm.Dependencies (LlvmDependency)
import Llvm.Instructions (LlvmStatement)
import Llvm.Ir (IR (toLlvm))
import Llvm.Types (LlvmFnAttr, LlvmType, fnAttrToLlvm)

data LlvmModule = LlvmModule
    { moduleName :: String
    , moduleFunctions :: [LlvmFunction]
    , moduleDependencies :: [LlvmDependency]
    , moduleGlobals :: [LlvmGlobal]
    , moduleTypeDefs :: [LlvmTypeDef]
    -- ^ Named struct type definitions (e.g., %Point = type { i32, i32 })
    }
    deriving (Show)

-- | Named struct type definition
data LlvmTypeDef = LlvmTypeDef
    { typeDefName :: String
    -- ^ The type name (without %)
    , typeDefFields :: [LlvmType]
    -- ^ The field types
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
    toLlvm (LlvmModule _ functions dependencies globals typeDefs) =
        unlines (map toLlvm $ nub dependencies)
            ++ "\n"
            ++ (if null typeDefs then "" else unlines (map toLlvm typeDefs) ++ "\n")
            ++ unlines (map toLlvm globals)
            ++ "\n\n"
            ++ unlines (map toLlvm functions)

instance IR LlvmTypeDef where
    toLlvm (LlvmTypeDef name fields) =
        "%" ++ name ++ " = type { " ++ intercalate ", " (map toLlvm fields) ++ " }"

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
