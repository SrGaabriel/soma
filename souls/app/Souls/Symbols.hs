{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE RecordWildCards #-}

module Souls.Symbols where

import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe, mapMaybe)
import qualified Data.Text as T
import Format.Trees (treeShow)
import Language.LSP.Protocol.Types (CompletionItem (..), CompletionItemKind (CompletionItemKind_Function), CompletionList (CompletionList), Hover (Hover), Location (..), MarkupContent (..), MarkupKind (..), Position, filePathToUri, type (|?) (InL))
import Project.Extracts (extractSymbolImports, filterSymbolsByNames)
import Project.Symbols (Symbol (..))
import Souls.Loc (findExprAtPos, findSymbolAtPos, lspPositionToOffset, spanToRange)
import Souls.Server (LspCompiledModule (..), findModuleByName)

getDefinitionAt ::
    Position ->
    LspCompiledModule ->
    Map.Map FilePath LspCompiledModule ->
    Maybe Location
getDefinitionAt pos LspCompiledModule{..} allCompiled = do
    sym <- findSymbolAtPos (lspPositionToOffset lcmSourceContent pos) lcmResolvedAst
    let defModule = resolvedSymbolModule sym
        span' = resolvedSymbolSpan sym
    if defModule == lcmModuleName
        then
            Just $ Location (filePathToUri lcmFilePath) (spanToRange lcmSourceContent span')
        else
            findSymbolModule sym defModule allCompiled

findSymbolModule :: Symbol -> String -> Map.Map FilePath LspCompiledModule -> Maybe Location
findSymbolModule sym defModuleName allCompiled =
    listToMaybe $ mapMaybe checkModule $ Map.toList allCompiled
  where
    checkModule (path, LspCompiledModule{..})
        | lcmModuleName == defModuleName =
            let span' = resolvedSymbolSpan sym
            in Just $ Location (filePathToUri path) (spanToRange lcmSourceContent span')
        | otherwise = Nothing

getHoverAt :: Position -> LspCompiledModule -> Maybe Hover
getHoverAt pos LspCompiledModule{..} = do
    let offset = lspPositionToOffset lcmSourceContent pos
    expr <- findExprAtPos offset lcmResolvedAst
    case Map.lookup expr lcmTypeMap of
        Just typ ->
            let typeStr = treeShow typ
                markdown =
                    MarkupContent
                        MarkupKind_Markdown
                        (T.pack $ "```soma\n" ++ typeStr ++ "\n```")
            in Just $ Hover (InL markdown) Nothing
        Nothing -> Nothing

getCompletions :: LspCompiledModule -> Map.Map FilePath LspCompiledModule -> CompletionList
getCompletions cm allCompiled =
    let localSyms = Map.keys (lcmPublicSymbols cm)
        importedSyms = concatMap getImportedSyms (extractSymbolImports (lcmResolvedAst cm))
        allSyms = localSyms ++ importedSyms
        items = map symbolToItem allSyms
    in CompletionList False Nothing items
  where
    getImportedSyms (modName, symNames) =
        case findModuleByName modName allCompiled of
            Just matchedModule ->
                let filtered = filterSymbolsByNames symNames (lcmPublicSymbols matchedModule)
                in Map.keys filtered
            Nothing -> []

symbolToItem :: Symbol -> CompletionItem
symbolToItem sym =
    CompletionItem
        { _label = T.pack $ resolvedSymbolName sym
        , _labelDetails = Nothing
        , _kind = Just CompletionItemKind_Function
        , _tags = Nothing
        , _detail = Nothing
        , _documentation = Nothing
        , _deprecated = Nothing
        , _preselect = Nothing
        , _sortText = Nothing
        , _filterText = Nothing
        , _insertText = Nothing
        , _insertTextFormat = Nothing
        , _insertTextMode = Nothing
        , _textEdit = Nothing
        , _textEditText = Nothing
        , _additionalTextEdits = Nothing
        , _commitCharacters = Nothing
        , _command = Nothing
        , _data_ = Nothing
        }

clItems :: CompletionList -> [CompletionItem]
clItems (CompletionList _ _ items) = items
