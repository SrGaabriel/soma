{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}

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

import Typing.Types (
    SkolemVar (..),
    TyConstructor (..),
    TyVar (..),
    Type (..),
 )

sanitizeTypeName :: Type -> String
sanitizeTypeName = \case
    TConstructor (TypeConstructor name _) -> name
    TApp (TConstructor (TypeConstructor "Array" _)) elemTy ->
        "Array$" ++ sanitizeTypeName elemTy
    TApp f arg ->
        sanitizeTypeName f ++ "$" ++ sanitizeTypeName arg
    TArrow argTy retTy ->
        "Fn$" ++ sanitizeTypeName argTy ++ "$" ++ sanitizeTypeName retTy
    TVar (TypeVar tvId _) -> "T" ++ tvId
    TSkolem (SkolemVar{skId}) -> "S" ++ skId
    TUnresolved name -> "Unresolved$" ++ name

makeDictParamName :: String -> Type -> String
makeDictParamName className ty =
    "dict$" ++ className ++ "$" ++ sanitizeTypeName ty

makeDictGlobalName :: String -> Type -> String
makeDictGlobalName className ty =
    "dict$" ++ className ++ "$" ++ sanitizeTypeName ty

makeDictStructTypeName :: String -> String
makeDictStructTypeName className = className ++ "$Dict"

makeInstanceMethodName :: String -> String -> String
makeInstanceMethodName methodName typeName = methodName ++ "$" ++ typeName

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
    case break (== '$') name of
        (methodName, '$' : typeName)
            | not (null methodName) && not (null typeName) ->
                Just (methodName, typeName)
        _ -> Nothing
