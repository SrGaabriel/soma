{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE RecordWildCards #-}

module Souls.Symbols where

import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe, mapMaybe)
import qualified Data.Text as T
import Format.Trees (treeShow)
import Language.LSP.Protocol.Types (CompletionItem (..), CompletionItemKind (CompletionItemKind_Function), CompletionList (CompletionList), Hover (Hover), Location (..), MarkupContent (..), MarkupKind (..), Position, filePathToUri, type (|?) (InL))
import Lexing.Position (Span (..))
import Metal.Expr (MCaseArm (..), MetallicExpr (..), TypedExpr, exprSpan, getMetallicExprType)
import Project.Extracts (extractSymbolImports, filterSymbolsByNames)
import Project.Symbols (Symbol (..))
import Souls.Loc (findSymbolAtPos, lspPositionToOffset, spanToRange)
import Souls.Server (LspCompiledModule (..), findModuleByName)
import Typing.Types (QualifiedType (..), Type)

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
    -- Search typed bindings for an expression at this position
    typ <- findTypeAtOffset offset lcmTypedBindings
    let typeStr = treeShow typ
        markdown =
            MarkupContent
                MarkupKind_Markdown
                (T.pack $ "```soma\n" ++ typeStr ++ "\n```")
    Just $ Hover (InL markdown) Nothing

-- | Find the type of the innermost expression at a given offset
findTypeAtOffset :: Int -> [(String, TypedExpr, [Type], Type, a, b, c)] -> Maybe QualifiedType
findTypeAtOffset offset bindings =
    listToMaybe $ mapMaybe (findInBinding offset) bindings

findInBinding :: Int -> (String, TypedExpr, [Type], Type, a, b, c) -> Maybe QualifiedType
findInBinding offset (_, body, _, _, _, _, _) = findInTypedExpr offset body

-- | Find the innermost TypedExpr containing the offset and return its type
findInTypedExpr :: Int -> TypedExpr -> Maybe QualifiedType
findInTypedExpr offset expr =
    let Span start' end' = exprSpan expr
    in if offset >= start' && offset < end'
        then case findInChildren offset expr of
            Just t -> Just t
            Nothing -> Just $ Forall [] [] (getMetallicExprType expr)
        else Nothing

-- | Search children of a TypedExpr for a more specific match
findInChildren :: Int -> TypedExpr -> Maybe QualifiedType
findInChildren offset expr =
    listToMaybe $ mapMaybe (findInTypedExpr offset) (typedExprChildren expr)

-- | Get the immediate children of a TypedExpr
typedExprChildren :: TypedExpr -> [TypedExpr]
typedExprChildren expr = case expr of
    MVar{} -> []
    MLit{} -> []
    MCall callee args _ _ -> callee : args
    MTypeApp e _ _ _ -> [e]
    MLet _ val body _ _ -> [val, body]
    MLambda _ body _ _ -> [body]
    MClosure{} -> []
    MConstruct _ _ args _ _ -> args
    MArrayLit elems _ _ -> elems
    MTuple elems _ _ -> elems
    MIf cond thenE elseE _ _ -> [cond, thenE, elseE]
    MCase scruts arms mdef _ _ ->
        scruts ++ map (\(MCaseArm _ b) -> b) arms ++ maybe [] (: []) mdef
    MFieldAccess e _ _ _ -> [e]
    MPanic{} -> []

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
