module Llvm.Dependencies where

import Data.List (intercalate)
import Llvm.Ir (IR (toLlvm))
import Llvm.Types (LlvmType)
import Llvm.Values (LlvmValue, getValueType)

data LlvmDependency
    = LlvmFunctionDependency
        { depName :: String
        , depReturnType :: LlvmType
        , depParams :: [LlvmType]
        }
    | LlvmConstantDependency
        { constantName :: String
        , constantValue :: LlvmValue
        , constantLinkage :: Maybe LinkageType
        }
    | LlvmStructDependency
        { structName :: String
        , structFields :: [LlvmType]
        }
    | LlvmGlobalDependency
        { globalName :: String
        , globalType :: LlvmType
        }
    deriving (Show, Eq)

data LinkageType
    = ExternalLinkage
    | InternalLinkage
    | PrivateLinkage
    | WeakLinkage
    | WeakODRLinkage
    | LinkOnceLinkage
    | LinkOnceODRLinkage
    deriving (Show, Eq)

instance IR LlvmDependency where
    toLlvm (LlvmFunctionDependency name retType params) =
        "declare "
            ++ toLlvm retType
            ++ " @"
            ++ name
            ++ "("
            ++ intercalate "," (map toLlvm params)
            ++ ")"
    toLlvm (LlvmConstantDependency name value linkage) =
        "@" ++ name ++ "=" ++ maybe "" toLlvm linkage ++ " unnamed_addr constant " ++ toLlvm (getValueType value) ++ " " ++ toLlvm value
    toLlvm (LlvmStructDependency name fields) =
        "%" ++ name ++ " = type {" ++ intercalate ", " (map toLlvm fields) ++ "}"
    toLlvm (LlvmGlobalDependency name ty) =
        "@" ++ name ++ " = external global " ++ toLlvm ty

instance IR LinkageType where
    toLlvm ExternalLinkage = "external"
    toLlvm InternalLinkage = "internal"
    toLlvm PrivateLinkage = "private"
    toLlvm WeakLinkage = "weak"
    toLlvm WeakODRLinkage = "weak_odr"
    toLlvm LinkOnceLinkage = "linkonce"
    toLlvm LinkOnceODRLinkage = "linkonce_odr"
