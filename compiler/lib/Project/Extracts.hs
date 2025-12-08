module Project.Extracts where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Inference.Core (InstanceEnv, TypeEnv)
import Project.Module (ModuleName)
import Project.Symbols (Symbol (resolvedSymbolName))
import Syntax.Tree (Expr (..), exprChildren)
import Typing.Types (QualifiedType)

extractSymbolImports :: Expr -> [(String, [String])]
extractSymbolImports (ExprRoot cs) = concatMap extractSymbolImports cs
extractSymbolImports (ExprImport name elements _) =
    [(name, elements)]
extractSymbolImports e = concatMap extractSymbolImports (exprChildren e)

extractExportList :: Expr -> Maybe [String]
extractExportList (ExprRoot cs) =
    case concatMap extractExportList' cs of
        [] -> Nothing
        exports -> Just (concat exports)
  where
    extractExportList' (ExprExport names _) = [names]
    extractExportList' _ = []
extractExportList _ = Nothing

extractIntrinsicNames :: Expr -> Set.Set String
extractIntrinsicNames root =
    Set.fromList [intrinsicName e | e@ExprIntrinsicDef{} <- exprChildren root]

filterSymbolsByNames :: [String] -> Map.Map Symbol QualifiedType -> Map.Map Symbol QualifiedType
filterSymbolsByNames names =
    Map.filterWithKey (\sym _ -> resolvedSymbolName sym `elem` names)

resolveImport ::
    Map ModuleName (TypeEnv, InstanceEnv) ->
    Map String TypeEnv ->
    Map String InstanceEnv ->
    (ModuleName, [String]) ->
    (Map Symbol QualifiedType, InstanceEnv)
resolveImport compiledDeps externalDeps externalInstances (impMod, mSyms) =
    case Map.lookup impMod compiledDeps of
        Just (publicSymbols, publicInstances) ->
            (filterSymbolsByNames mSyms publicSymbols, publicInstances)
        Nothing ->
            let symbols = maybe Map.empty (filterSymbolsByNames mSyms) (Map.lookup impMod externalDeps)
                instances = fromMaybe Map.empty (Map.lookup impMod externalInstances)
            in (symbols, instances)
