{-# LANGUAGE LambdaCase #-}

module Alloy.DictUtils (
    sanitizeTypeName,
    makeDictParamName,
    makeDictGlobalName,
    makeDictStructTypeName,
    makeInstanceMethodName,
    extractClassName,
    extractTypeArgs,
    extractInstanceType,
    extractBaseTypeName,
    parseInstanceMethodName,
) where

import Alloy.Naming (
    makeDictGlobalName,
    makeDictParamName,
    makeDictStructTypeName,
    makeInstanceMethodName,
    nameSeparator,
    sanitizeTypeName,
 )
import Typing.Types (
    TyConstructor (..),
    Type (..),
 )
import Utils.Lists (hardHead)

extractClassName :: Type -> Maybe String
extractClassName = \case
    TConstructor (TypeConstructor name _) -> Just name
    TApp ty _ -> extractClassName ty
    _ -> Nothing

extractTypeArgs :: Type -> [Type]
extractTypeArgs ty = reverse (go ty [])
  where
    go (TApp l r) acc = go l (r : acc)
    go (TConstructor _) acc = acc
    go _ acc = acc

extractInstanceType :: Type -> Maybe Type
extractInstanceType = \case
    TApp _ instanceTy -> Just instanceTy
    TConstructor _ -> Nothing
    _ -> Nothing

extractBaseTypeName :: Type -> Maybe String
extractBaseTypeName = \case
    TConstructor (TypeConstructor name _) -> Just name
    TApp (TConstructor (TypeConstructor name _)) _ -> Just name
    TApp f _ -> extractBaseTypeName f
    _ -> Nothing

parseInstanceMethodName :: String -> Maybe (String, String)
parseInstanceMethodName name =
    case break (== hardHead nameSeparator) name of
        (methodName, sep : typeName)
            | [hardHead nameSeparator] == [sep] && not (null methodName) && not (null typeName) ->
                Just (methodName, typeName)
        _ -> Nothing
