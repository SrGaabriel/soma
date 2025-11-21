{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import Control.Concurrent.STM
import Control.Lens ((^.))
import Control.Monad.IO.Class
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe, mapMaybe)
import qualified Data.Text as T
import Inference.Assembler (inferTree)
import Inference.Core (TypeMap)
import Inference.Resolver (runResolverWithEnv)
import Language.LSP.Diagnostics
import Language.LSP.Protocol.Lens
import Language.LSP.Protocol.Message
import Language.LSP.Protocol.Types
import Language.LSP.Server
import Language.LSP.VFS
import Lexing.Lexer (lexCode)
import Lexing.Position (Span (..))
import Logging.ErrorPrinter (PrintableError (..))
import Logging.PrettyTrees (treeShow)
import Parsing.Ast (parse)
import Project.Graph
import Project.Incremental
import Project.Symbols (Symbol, resolvedSymbolName, resolvedSymbolSpan)
import Syntax.Tree (Expr (..), exprChildren, exprSpan)
import System.FilePath
import Typing.Types (QualifiedType)

data LspCompiledModule = LspCompiledModule
    { lcmModuleName :: String
    , lcmResolvedAst :: Expr
    , lcmTypeMap :: TypeMap
    , lcmPublicSymbols :: Map.Map Symbol QualifiedType
    , lcmSourceContent :: T.Text
    }

data LspState = LspState
    { stateModules :: TVar (Map.Map FilePath LspCompiledModule)
    , stateWorkspaceRoot :: TVar (Maybe FilePath)
    , stateModuleGraph :: TVar (Maybe ModuleGraph)
    }

main :: IO Int
main = do
    modulesVar <- newTVarIO Map.empty
    workspaceVar <- newTVarIO Nothing
    graphVar <- newTVarIO Nothing

    let state = LspState modulesVar workspaceVar graphVar

    runServer
        $ ServerDefinition
            { onConfigChange = const $ pure ()
            , defaultConfig = ()
            , configSection = T.pack "soma"
            , parseConfig = const $ const $ Right ()
            , doInitialize = \env req -> do
                let mRootUri = req ^. params . rootUri
                case mRootUri of
                    (InL uri) -> do
                        case uriToFilePath uri of
                            Just path -> liftIO $ do
                                atomically $ writeTVar workspaceVar (Just path)
                                mods <- findModules "workspace" path
                                graphE <- buildModuleGraph mods
                                case graphE of
                                    Right graph -> atomically $ writeTVar graphVar (Just graph)
                                    Left _ -> return ()
                            Nothing -> pure ()
                    _ -> pure ()
                pure $ Right env
            , staticHandlers = handlers state
            , interpretHandler = \env -> Iso (runLspT env) liftIO
            , Language.LSP.Server.options = defaultOptions
            }

handlers :: LspState -> ClientCapabilities -> Handlers (LspM ())
handlers state _caps =
    mconcat
        [ notificationHandler SMethod_Initialized $ \_msg ->
            sendNotification SMethod_WindowShowMessage
                $ ShowMessageParams MessageType_Info "Soma LSP initialized"
        , notificationHandler SMethod_TextDocumentDidOpen $ \msg -> do
            let fileUri = msg ^. params . textDocument . uri
            analyzeFile state fileUri
        , notificationHandler SMethod_TextDocumentDidChange $ \msg -> do
            let fileUri = msg ^. params . textDocument . uri
            analyzeFile state fileUri
        , requestHandler SMethod_TextDocumentHover (handleHover state)
        , requestHandler SMethod_TextDocumentDefinition (handleGotoDefinition state)
        , requestHandler SMethod_TextDocumentCompletion (handleCompletion state)
        ]

analyzeFile :: LspState -> Uri -> LspM () ()
analyzeFile LspState{..} fileUri = do
    let nUri = toNormalizedUri fileUri
    mdoc <- getVirtualFile nUri

    case (mdoc, uriToFilePath fileUri) of
        (Just vf, Just filePath) -> do
            let content = virtualFileText vf
                modName = dropExtension $ takeFileName filePath
            let (tokens, lexErrors) = lexCode content

            case parse tokens of
                Left parseErrs -> do
                    let diags = map (errorToDiagnostic content) lexErrors ++ map (errorToDiagnostic content) parseErrs
                    Language.LSP.Server.publishDiagnostics 100 nUri Nothing (partitionBySource diags)
                Right ast -> do
                    compiledMods <- liftIO $ readTVarIO stateModules

                    result <-
                        liftIO
                            $ compileModuleForLSP
                                modName
                                filePath
                                (T.unpack content)
                                ast
                                compiledMods

                    case result of
                        Left errors -> do
                            let diags = map (errorToDiagnostic content) errors
                            Language.LSP.Server.publishDiagnostics 100 nUri Nothing (partitionBySource diags)
                        Right compiled -> do
                            liftIO
                                $ atomically
                                $ modifyTVar stateModules (Map.insert filePath compiled)
                            Language.LSP.Server.publishDiagnostics 100 nUri Nothing (partitionBySource [])
        _ -> pure ()

compileModuleForLSP ::
    String ->
    FilePath ->
    String ->
    Expr ->
    Map.Map FilePath LspCompiledModule ->
    IO (Either [SomeError] LspCompiledModule)
compileModuleForLSP modName _path content ast compiledDeps = do
    let imports = extractSymbolImports ast
        seedEnv = Map.unions $ map resolveImport imports

    resolvedResult <- runResolverWithEnv "lsp" modName seedEnv ast
    case resolvedResult of
        Left err -> return $ Left [SomeError err]
        Right (resolvedAst, fullEnv, instanceEnv) -> do
            let typesResult = inferTree "lsp" modName fullEnv instanceEnv resolvedAst

            case typesResult of
                Left errs -> return $ Left (map SomeError errs)
                Right types -> do
                    let newDefs = Map.difference fullEnv seedEnv

                    return
                        $ Right
                        $ LspCompiledModule
                            { lcmModuleName = modName
                            , lcmResolvedAst = resolvedAst
                            , lcmTypeMap = types
                            , lcmPublicSymbols = newDefs
                            , lcmSourceContent = T.pack content
                            }
  where
    resolveImport (impMod, syms) =
        case Map.lookup impMod compiledDeps of
            Just LspCompiledModule{..} ->
                filterSymbolsByNames syms lcmPublicSymbols
            Nothing -> Map.empty

data SomeError = forall e. (PrintableError e) => SomeError e

instance PrintableError SomeError where
    errorStart (SomeError e) = errorStart e
    errorEnd (SomeError e) = errorEnd e
    errorMessage (SomeError e) = errorMessage e

errorToDiagnostic :: (PrintableError e) => T.Text -> e -> Diagnostic
errorToDiagnostic code err =
    Diagnostic
        { _range =
            Range
                (offsetToPosition code (errorStart err))
                (offsetToPosition code (errorEnd err))
        , _severity = Just DiagnosticSeverity_Error
        , _code = Nothing
        , _codeDescription = Nothing
        , _source = Just "soma"
        , _message = T.pack $ errorMessage err
        , _tags = Nothing
        , _relatedInformation = Nothing
        , _data_ = Nothing
        }

handleHover ::
    LspState ->
    TRequestMessage 'Method_TextDocumentHover ->
    (Either (TResponseError 'Method_TextDocumentHover) (Hover |? Null) -> LspM () ()) ->
    LspM () ()
handleHover LspState{..} req responder = do
    let pos = req ^. params . position
        fileUri = req ^. params . textDocument . uri

    case uriToFilePath fileUri of
        Just filePath -> do
            compiled <- liftIO $ readTVarIO stateModules
            case Map.lookup filePath compiled of
                Just cm -> do
                    let mHover = getHoverAt pos cm
                    responder $ Right $ maybe (InR Null) InL mHover
                Nothing -> responder $ Right $ InR Null
        Nothing -> responder $ Right $ InR Null

getHoverAt :: Position -> LspCompiledModule -> Maybe Hover
getHoverAt pos LspCompiledModule{..} = do
    let offset = lspPositionToOffset lcmSourceContent pos 
    expr <- findExprAtPos offset lcmResolvedAst
    typ <- Map.lookup expr lcmTypeMap
    let typeStr = treeShow typ
        markdown =
            MarkupContent
                MarkupKind_Markdown
                (T.pack $ "```soma\n" ++ typeStr ++ "\n```")
    return $ Hover (InL markdown) Nothing

handleGotoDefinition ::
    LspState ->
    TRequestMessage 'Method_TextDocumentDefinition ->
    (Either (TResponseError 'Method_TextDocumentDefinition) (Definition |? [DefinitionLink] |? Null) -> LspM () ()) ->
    LspM () ()
handleGotoDefinition LspState{..} req responder = do
    let pos = req ^. params . position
        fileUri = req ^. params . textDocument . uri

    case uriToFilePath fileUri of
        Just filePath -> do
            compiled <- liftIO $ readTVarIO stateModules
            case Map.lookup filePath compiled of
                Just cm -> do
                    let mLoc = getDefinitionAt pos cm compiled
                    responder
                        $ Right
                        $ maybe
                            (InR $ InR Null)
                            (InL . Definition . InL)
                            mLoc
                Nothing -> responder $ Right $ InR $ InR Null
        Nothing -> responder $ Right $ InR $ InR Null

getDefinitionAt ::
    Position ->
    LspCompiledModule ->
    Map.Map FilePath LspCompiledModule ->
    Maybe Location
getDefinitionAt pos LspCompiledModule{..} allCompiled = do
    sym <- findSymbolAtPos (lspPositionToOffset lcmSourceContent pos) lcmResolvedAst

    case Map.lookup sym lcmPublicSymbols of
        Just _ ->
            let span = resolvedSymbolSpan sym
            in Just $ Location (filePathToUri "current") (spanToRange lcmSourceContent span)
        Nothing ->
            findSymbolInDeps sym allCompiled

findSymbolInDeps :: Symbol -> Map.Map FilePath LspCompiledModule -> Maybe Location
findSymbolInDeps sym allCompiled =
    listToMaybe $ mapMaybe checkModule $ Map.toList allCompiled
  where
    checkModule (path, LspCompiledModule{..}) = do
        _ <- Map.lookup sym lcmPublicSymbols
        let span = resolvedSymbolSpan sym
        return $ Location (filePathToUri path) (spanToRange lcmSourceContent span)

handleCompletion ::
    LspState ->
    TRequestMessage 'Method_TextDocumentCompletion ->
    (Either (TResponseError 'Method_TextDocumentCompletion) ([CompletionItem] |? CompletionList |? Null) -> LspM () ()) ->
    LspM () ()
handleCompletion LspState{..} req responder = do
    let fileUri = req ^. params . textDocument . uri

    case uriToFilePath fileUri of
        Just filePath -> do
            compiled <- liftIO $ readTVarIO stateModules
            case Map.lookup filePath compiled of
                Just cm -> do
                    let completions = getCompletions cm compiled
                    responder $ Right $ InR (InL completions)
                Nothing ->
                    responder $ Right $ InR (InL $ CompletionList False Nothing [])
        Nothing ->
            responder $ Right $ InR (InL $ CompletionList False Nothing [])

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

findModuleByName :: String -> Map.Map FilePath LspCompiledModule -> Maybe LspCompiledModule
findModuleByName name mods =
    listToMaybe [cm | cm <- Map.elems mods, lcmModuleName cm == name]

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

spanToRange :: T.Text -> Span -> Range
spanToRange code (Span start end) =
    Range (offsetToPosition code start) (offsetToPosition code end)

lspPositionToOffset :: T.Text -> Position -> Int
lspPositionToOffset text (Position line col) =
    let linesList = T.lines text
        precedingChars = sum $ map (\l -> T.length l + 1) (take (fromIntegral line) linesList)
    in precedingChars + (fromIntegral col)

offsetToPosition :: T.Text -> Int -> Position
offsetToPosition text offset =
    let
        (prefix, _) = T.splitAt offset text
        line = fromIntegral $ T.count "\n" prefix
        col = fromIntegral $ T.length $ T.takeWhileEnd (/= '\n') prefix
    in Position line col

findExprAtPos :: Int -> Expr -> Maybe Expr
findExprAtPos offset expr =
    case expr of
        e | exprContainsOffset offset e -> Just e
        _ -> listToMaybe $ mapMaybe (findExprAtPos offset) (exprChildren expr)
  where
    exprContainsOffset off e =
        let Span start end = exprSpan e
        in off >= start && off <= end

findSymbolAtPos :: Int -> Expr -> Maybe Symbol
findSymbolAtPos offset = go
  where
    go (ExprVar sym span)
        | offsetInSpan offset span = Just sym
    go expr = listToMaybe $ mapMaybe go (exprChildren expr)

    offsetInSpan off (Span start end) = off >= start && off <= end
