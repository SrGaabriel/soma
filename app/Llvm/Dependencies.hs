module Llvm.Dependencies where

import Llvm.Types (LlvmType)
import Llvm.Ir (IR (toLlvm))
import Llvm.Values (LlvmValue, getValueType)
import Data.List (intercalate)

data LlvmDependency
    = LlvmFunction
        { depName :: String
        , depReturnType :: LlvmType
        , depParams :: [LlvmType]
        }
    | LlvmConstant
        { constantName :: String
        , constantValue :: LlvmValue
        , constantLinkage :: Maybe LinkageType
        }
    | LlvmStruct
        { structName :: String
        , structFields :: [LlvmType]
        }
    deriving (Show, Eq)

data LinkageType
    = External
    | Internal
    | Private
    | Weak
    | WeakODR
    | LinkOnce
    | LinkOnceODR
    deriving (Show, Eq)

instance IR LlvmDependency where
    toLlvm (LlvmFunction name retType params) =
        "declare " ++ toLlvm retType ++ " @" ++ name ++ "(" ++
        intercalate "," (map toLlvm params) ++ ")"
    toLlvm (LlvmConstant name value linkage) =
        "@" ++ name ++ "=" ++ maybe "" toLlvm linkage ++ " unnamed_addr constant " ++ toLlvm (getValueType value) ++ " " ++ toLlvm value
    toLlvm (LlvmStruct name fields) =
        "%" ++ name ++ " = type {" ++ intercalate ", " (map toLlvm fields) ++ "}"

instance IR LinkageType where
    toLlvm External = "external"
    toLlvm Internal = "internal"
    toLlvm Private = "private"
    toLlvm Weak = "weak"
    toLlvm WeakODR = "weak_odr"
    toLlvm LinkOnce = "linkonce"
    toLlvm LinkOnceODR = "linkonce_odr"