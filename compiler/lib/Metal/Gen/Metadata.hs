{-# LANGUAGE NamedFieldPuns #-}

module Metal.Gen.Metadata (
    extractConstructorMetadata,
    SymbolEnv,
) where

import Data.Map (Map)
import qualified Data.Map as Map
import Lexing.Position (Located (..))
import Metal.Metadata
import Project.Name (Name (..))
import Project.Symbols (Symbol (..), SymbolKind (..))
import Syntax.Tree
import Typing.Types (QualifiedType)

-- | Symbol environment from the resolver
type SymbolEnv = Map Symbol QualifiedType

{- | Extract constructor metadata from the AST
Takes the symbol environment to look up proper Names for types
-}
extractConstructorMetadata :: SymbolEnv -> Expr -> Map Name MetallicConstructorMetadata
extractConstructorMetadata symEnv (ExprRoot decls) =
    Map.fromList $ concat [extractFromDataType dt | dt@(ExprDataTypeDef{}) <- decls]
  where
    extractFromDataType (ExprDataTypeDef{dataName, dataConstructors}) =
        let typeName = lookupTypeName dataName symEnv
        in [ (ctorName', MetallicConstructorMetadata typeName tag fieldTypes)
           | ( tag
                , ExprDataConstructor
                    { structConstructorName = ctorName
                    , structConstructorArgs = fields
                    }
                ) <-
                zip [0 ..] dataConstructors
           , let fieldTypes = map (lValue . snd) fields
           , let ctorName' = lookupConstructorName ctorName dataName symEnv
           ]
    extractFromDataType _ = []
extractConstructorMetadata _ _ = Map.empty

lookupTypeName :: String -> SymbolEnv -> Name
lookupTypeName name env =
    case findSymbolByName name TypeSymbol env of
        Just sym -> symbolToName sym
        Nothing -> error $ "lookupTypeName: Type not found in environment: " ++ name

lookupConstructorName :: String -> String -> SymbolEnv -> Name
lookupConstructorName ctorName parentTypeName env =
    case findSymbolByNameAndKind ctorName (DataConstructorSymbol parentTypeName) env of
        Just sym -> symbolToName sym
        Nothing -> error $ "lookupConstructorName: Constructor not found: " ++ ctorName

findSymbolByName :: String -> SymbolKind -> SymbolEnv -> Maybe Symbol
findSymbolByName name kind env =
    case [sym | sym <- Map.keys env, resolvedSymbolName sym == name, resolvedSymbolKind sym == kind] of
        (sym : _) -> Just sym
        [] -> Nothing

findSymbolByNameAndKind :: String -> SymbolKind -> SymbolEnv -> Maybe Symbol
findSymbolByNameAndKind name kind env =
    case [sym | sym <- Map.keys env, resolvedSymbolName sym == name, resolvedSymbolKind sym == kind] of
        (sym : _) -> Just sym
        [] -> Nothing

symbolToName :: Symbol -> Name
symbolToName sym = case resolvedSymbolUnique sym of
    Just unique -> NUser unique
    Nothing -> error $ "symbolToName: Symbol without Unique: " ++ resolvedSymbolName sym
