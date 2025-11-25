{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}

module Alloy.Naming (
    nameSeparator,
    nameTypeSuffix,
    nameDictPrefix,
    nameDictSuffix,
    nameTyVarPrefix,
    nameSkolemPrefix,
    nameUnresolvedPrefix,
    nameArrayPrefix,
    nameFunctionPrefix,
    nameParamSeparator,
    nameEnvParam,
    nameTmpPrefix,
    nameBlockPrefix,
    sanitizeTypeName,
    sanitizeIdentifier,
    encodeTypeName,
    makeModuleHash,
    qualifyWithModule,
    makeDictParamName,
    makeDictGlobalName,
    makeDictStructTypeName,
    makeInstanceMethodName,
    makeMonomorphicName,
    makeRefParamName,
    extractTypeName,
    extractBaseTypeName,
) where

import Data.Char (isAlphaNum)
import Data.Hashable (hash)
import Data.List (intercalate)
import Inference.Naming (nameSkolemPrefix, nameTmpPrefix)
import Typing.Types (
    SkolemVar (..),
    TyConstructor (..),
    TyVar (..),
    Type (..),
 )

nameSeparator :: String
nameSeparator = "$"

nameTypeSuffix :: String
nameTypeSuffix = "$"

nameDictPrefix :: String
nameDictPrefix = "dict$"

nameDictSuffix :: String
nameDictSuffix = "$Dict"

nameTyVarPrefix :: String
nameTyVarPrefix = "T"

nameUnresolvedPrefix :: String
nameUnresolvedPrefix = "Unresolved$"

nameArrayPrefix :: String
nameArrayPrefix = "Array$"

nameFunctionPrefix :: String
nameFunctionPrefix = "Fn$"

nameParamSeparator :: String
nameParamSeparator = "$in$"

nameEnvParam :: String
nameEnvParam = "$env"

nameBlockPrefix :: String
nameBlockPrefix = "block"

sanitizeTypeName :: Type -> String
sanitizeTypeName = \case
    TConstructor (TypeConstructor name _) -> name
    TApp (TConstructor (TypeConstructor "Array" _)) elemTy ->
        nameArrayPrefix ++ sanitizeTypeName elemTy
    TApp f arg ->
        sanitizeTypeName f ++ nameSeparator ++ sanitizeTypeName arg
    TArrow argTy retTy ->
        nameFunctionPrefix ++ sanitizeTypeName argTy ++ nameSeparator ++ sanitizeTypeName retTy
    TVar (TypeVar tvId _) -> nameTyVarPrefix ++ tvId
    TSkolem (SkolemVar{skId}) -> nameSkolemPrefix ++ skId
    TUnresolved name -> nameUnresolvedPrefix ++ name

sanitizeIdentifier :: String -> String
sanitizeIdentifier = map (\c -> if isAlphaNum c then c else '_')

encodeTypeName :: Type -> String
encodeTypeName t =
    case t of
        TVar (TypeVar v _) -> "v_" ++ sanitizeIdentifier v
        TSkolem _ -> "sk"
        TConstructor c -> sanitizeIdentifier (tcName c)
        TApp a b -> encodeTypeName a ++ "_" ++ encodeTypeName b
        TArrow a b -> "fn_" ++ encodeTypeName a ++ "_to_" ++ encodeTypeName b
        TUnresolved s -> "u_" ++ sanitizeIdentifier s

makeModuleHash :: String -> String
makeModuleHash moduleName =
    let h = abs (hash moduleName)
        shortHash = take 8 (show h)
    in "m" ++ shortHash

qualifyWithModule :: String -> String -> String
qualifyWithModule moduleName baseName =
    baseName ++ nameSeparator ++ makeModuleHash moduleName

makeDictParamName :: String -> Type -> String
makeDictParamName className ty =
    nameDictPrefix ++ className ++ nameSeparator ++ sanitizeTypeName ty

makeDictGlobalName :: String -> String -> Type -> String
makeDictGlobalName moduleName className ty =
    nameDictPrefix ++ className ++ nameSeparator ++ sanitizeTypeName ty ++ nameSeparator ++ makeModuleHash moduleName

makeDictStructTypeName :: String -> String -> String
makeDictStructTypeName moduleName className =
    className ++ nameSeparator ++ makeModuleHash moduleName ++ nameDictSuffix

makeInstanceMethodName :: String -> String -> String
makeInstanceMethodName methodName typeName =
    methodName ++ nameSeparator ++ typeName

-- todo: review
makeMonomorphicName :: String -> String -> [Type] -> String
makeMonomorphicName _moduleName baseName typeArgs =
    let enc = intercalate "_" (map encodeTypeName typeArgs)
        mangledBase = if null typeArgs then baseName else baseName ++ nameSeparator ++ enc
    in mangledBase

makeRefParamName :: String -> String -> String
makeRefParamName refName blockName =
    refName ++ nameParamSeparator ++ blockName

extractTypeName :: Type -> String
extractTypeName (TConstructor (TypeConstructor name _)) = name
extractTypeName (TApp a b) = extractTypeName a ++ nameSeparator ++ extractTypeName b
extractTypeName _ = "Unknown"

extractBaseTypeName :: Type -> String
extractBaseTypeName (TConstructor (TypeConstructor name _)) = name
extractBaseTypeName (TApp a _) = extractBaseTypeName a
extractBaseTypeName _ = "Unknown"
