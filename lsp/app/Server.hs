{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

module LSP.Server where

import Control.Concurrent.STM
import Control.Lens ((^.))
import Control.Monad.IO.Class
import Project.Symbols
import Project.Module
import Project.Graph
import Syntax.Tree
import Lexing.Position (Span)
import Typing.Types
import Inference.Core
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import Language.LSP.Protocol.Lens
import Language.LSP.Protocol.Message
import Language.LSP.Protocol.Types
import Language.LSP.Server
import Language.LSP.VFS
import Language.LSP.Diagnostics
import System.FilePath
import Incremental

-- State now uses WorkspaceState from Incremental module
data LspState = LspState
    { stateWorkspace :: TVar WorkspaceState
    }

main :: IO Int
main = do
    -- Initialize with empty workspace
    initialWs <- return $ WorkspaceState Map.empty Map.empty Map.empty
    workspaceVar <- newTVarIO initialWs
    let state = LspState workspaceVar
    
    runServer $ ServerDefinition
        { onConfigChange = const $ pure ()
        , defaultConfig = ()
        , configSection = T.pack "soma"
        , parseConfig = const $ const $ Right ()
        , doInitialize = \env req -> do
            -- Initialize workspace when we know the root
            let rootPath = req ^. params . rootUri
            case rootPath of
                Just uri -> do
                    case uriToFilePath uri of
                        Just path -> do
                            liftIO $ putStrLn $ "Initializing workspace at: " ++ path
                            ws <- liftIO $ buildWorkspaceState path
                            liftIO $ atomically $ writeTVar workspaceVar ws
                            liftIO $ putStrLn $ "Workspace initialized with " ++ show (Map.size $ wsModules ws) ++ " modules"
                        Nothing -> pure ()
                Nothing -> pure ()
            pure $ Right env
        , staticHandlers = handlers state
        , interpretHandler = \env -> Iso (runLspT env) liftIO
        , Language.LSP.Server.options = defaultOptions
        }

handlers :: LspState -> ClientCapabilities -> Handlers (LspM ())
handlers state capabilities = mconcat
    [ notificationHandler SMethod_Initialized $ \_msg ->
        sendNotification SMethod_WindowShowMessage $
            ShowMessageParams MessageType_Info "Soma LSP Server initialized"
    
    , notificationHandler SMethod_TextDocumentDidOpen $ \msg -> do
        let doc = msg ^. params . textDocument
            fileUri = doc ^. uri
        -- When file opens, analyze it with dependency context
        analyzeAndPublishIncremental state fileUri
    
    , notificationHandler SMethod_TextDocumentDidChange $ \msg -> do
        let fileUri = msg ^. params . textDocument . uri
        -- Incremental update on change
        analyzeAndPublishIncremental state fileUri
    
    , notificationHandler SMethod_TextDocumentDidSave $ \msg -> do
        let fileUri = msg ^. params . textDocument . uri
        -- On save, potentially recompile dependents
        analyzeAndRecompileDependents state fileUri
    
    , requestHandler SMethod_TextDocumentHover $ \req responder -> do
        handleHover state req responder
    
    , requestHandler SMethod_TextDocumentDefinition $ \req responder -> do
        handleGotoDefinition state req responder
    
    , requestHandler SMethod_TextDocumentCompletion $ \req responder -> do
        handleCompletion state req responder
    
    , requestHandler SMethod_TextDocumentDocumentSymbol $ \req responder -> do
        handleDocumentSymbols state req responder
    ]

-- This now uses the incremental compilation from the Incremental module
analyzeAndPublishIncremental :: LspState -> Uri -> LspM () ()
analyzeAndPublishIncremental (LspState{..}) fileUri = do
    let nUri = toNormalizedUri fileUri
    mdoc <- getVirtualFile nUri
    
    case mdoc of
        Just vf -> do
            let text = T.unpack $ virtualFileText vf
                mFilePath = uriToFilePath fileUri
            
            case mFilePath of
                Just filePath -> do
                    -- Use incremental analysis which handles dependencies
                    ws <- liftIO $ readTVarIO stateWorkspace
                    newWs <- liftIO $ updateFile filePath text ws
                    liftIO $ atomically $ writeTVar stateWorkspace newWs
                    
                    -- Publish diagnostics for this file
                    case Map.lookup filePath (wsModules newWs) of
                        Just modState -> do
                            let diags = maDiagnostics (msAnalysis modState)
                            publishDiagnostics 100 nUri Nothing (partitionBySource diags)
                        Nothing -> pure ()
                
                Nothing -> pure ()
        Nothing -> pure ()

-- On save, recompile all affected modules and publish their diagnostics
analyzeAndRecompileDependents :: LspState -> Uri -> LspM () ()
analyzeAndRecompileDependents (LspState{..}) fileUri = do
    case uriToFilePath fileUri of
        Just filePath -> do
            ws <- liftIO $ readTVarIO stateWorkspace
            
            -- Find all files that depend on this one
            let dependents = findTransitiveDependents filePath (wsDependencyGraph ws)
            
            -- Recompile all affected modules
            newWs <- liftIO $ recompileAffected ws
            liftIO $ atomically $ writeTVar stateWorkspace newWs
            
            -- Publish diagnostics for all affected files
            forM_ (filePath : dependents) $ \affectedPath -> do
                case Map.lookup affectedPath (wsModules newWs) of
                    Just modState -> do
                        let uri = filePathToUri affectedPath
                            nUri = toNormalizedUri uri
                            diags = maDiagnostics (msAnalysis modState)
                        publishDiagnostics 100 nUri Nothing (partitionBySource diags)
                    Nothing -> pure ()
        Nothing -> pure ()

-- Hover support - now looks up in workspace state
handleHover :: LspState -> TRequestMessage 'Method_TextDocumentHover -> (Either ResponseError (Hover |? Null) -> LspM () ()) -> LspM () ()
handleHover (LspState{..}) req responder = do
    let pos = req ^. params . position
        fileUri = req ^. params . textDocument . uri
        mFilePath = uriToFilePath fileUri
    
    case mFilePath of
        Just filePath -> do
            ws <- liftIO $ readTVarIO stateWorkspace
            case Map.lookup filePath (wsModules ws) of
                Just modState -> do
                    let hoverInfo = getHoverInfo (msAnalysis modState) pos
                    responder $ Right $ maybe (InR Null) InL hoverInfo
                Nothing -> responder $ Right $ InR Null
        Nothing -> responder $ Right $ InR Null

getHoverInfo :: ModuleAnalysis -> Position -> Maybe Hover
getHoverInfo ModuleAnalysis{..} pos = do
    ast <- maAst
    typeMap <- maTypeMap
    
    -- Find the expression at the given position
    let expr = findExprAtPosition ast pos
    
    case expr of
        Just e -> do
            -- Look up type information
            exprType <- Map.lookup e typeMap
            let typeStr = prettyPrintType exprType
            let markdown = MarkupContent MarkupKind_Markdown (T.pack $ "```soma\n" ++ typeStr ++ "\n```")
            Just $ Hover (InL markdown) Nothing
        Nothing -> Nothing

-- Go to definition - handles cross-file navigation
handleGotoDefinition :: LspState -> TRequestMessage 'Method_TextDocumentDefinition -> (Either ResponseError (Definition |? (DefinitionLink |? Null)) -> LspM () ()) -> LspM () ()
handleGotoDefinition (LspState{..}) req responder = do
    let pos = req ^. params . position
        fileUri = req ^. params . textDocument . uri
        mFilePath = uriToFilePath fileUri
    
    case mFilePath of
        Just filePath -> do
            ws <- liftIO $ readTVarIO stateWorkspace
            case Map.lookup filePath (wsModules ws) of
                Just modState -> do
                    -- Find definition, potentially in another module
                    let defLocation = findDefinitionLocationInWorkspace ws modState pos
                    responder $ Right $ maybe (InR $ InR Null) (InL . Definition . InL) defLocation
                Nothing -> responder $ Right $ InR $ InR Null
        Nothing -> responder $ Right $ InR $ InR Null

-- Enhanced to search across workspace
findDefinitionLocationInWorkspace :: WorkspaceState -> ModuleState -> Position -> Maybe Location
findDefinitionLocationInWorkspace WorkspaceState{..} modState pos = do
    ast <- maAst (msAnalysis modState)
    
    -- Find symbol at cursor
    symbol <- findSymbolAtPosition ast pos
    
    -- Check if it's defined in current module
    let localEnv = maSymbolEnv (msAnalysis modState)
    case localEnv >>= Map.lookup symbol of
        Just _ -> 
            -- Local definition
            let defSpan = symbolSpan symbol
            in Just $ Location (symbolUri symbol) (spanToRange defSpan)
        Nothing -> 
            -- Search imported modules
            findInImportedModules symbol (msImports modState) wsModules

findInImportedModules :: Symbol -> [(String, [String])] -> Map.Map FilePath ModuleState -> Maybe Location
findInImportedModules symbol imports modules = 
    -- Search through imported modules for the symbol
    listToMaybe $ mapMaybe searchModule (Map.elems modules)
  where
    searchModule :: ModuleState -> Maybe Location
    searchModule ms = do
        env <- maSymbolEnv (msAnalysis ms)
        _ <- Map.lookup symbol env
        let defSpan = symbolSpan symbol
        Just $ Location (symbolUri symbol) (spanToRange defSpan)

-- Completion - now includes imported symbols
handleCompletion :: LspState -> TRequestMessage 'Method_TextDocumentCompletion -> (Either ResponseError (CompletionList |? (CompletionItem |? Null)) -> LspM () ()) -> LspM () ()
handleCompletion (LspState{..}) req responder = do
    let pos = req ^. params . position
        fileUri = req ^. params . textDocument . uri
        mFilePath = uriToFilePath fileUri
    
    case mFilePath of
        Just filePath -> do
            ws <- liftIO $ readTVarIO stateWorkspace
            case Map.lookup filePath (wsModules ws) of
                Just modState -> do
                    -- Get completions from current scope AND imported modules
                    let completions = getCompletionsWithImports ws modState pos
                    responder $ Right $ InL completions
                Nothing -> responder $ Right $ InL $ CompletionList False Nothing []
        Nothing -> responder $ Right $ InL $ CompletionList False Nothing []

getCompletionsWithImports :: WorkspaceState -> ModuleState -> Position -> CompletionList
getCompletionsWithImports WorkspaceState{..} modState _pos = 
    let localSymbols = case maSymbolEnv (msAnalysis modState) of
            Just env -> Map.keys env
            Nothing -> []
        
        -- Get symbols from imported modules
        importedSymbols = concatMap getImportedSymbols (msImports modState)
        
        allSymbols = localSymbols ++ importedSymbols
        items = map symbolToCompletionItem allSymbols
    in CompletionList False Nothing items
  where
    getImportedSymbols :: (String, [String]) -> [Symbol]
    getImportedSymbols (modName, symbolNames) =
        case findModuleByName modName wsModules of
            Just ms -> case maSymbolEnv (msAnalysis ms) of
                Just env -> filterSymbolsByNames symbolNames env & Map.keys
                Nothing -> []
            Nothing -> []
    
    findModuleByName :: String -> Map.Map FilePath ModuleState -> Maybe ModuleState
    findModuleByName name modules =
        -- Match module name to filepath
        listToMaybe $ filter (moduleMatches name) (Map.elems modules)
    
    moduleMatches :: String -> ModuleState -> Bool
    moduleMatches _name _ms = True  -- Implement proper matching

symbolToCompletionItem :: Symbol -> CompletionItem
symbolToCompletionItem sym =
    let label = T.pack $ resolvedSymbolName sym
    in CompletionItem
        { _label = label
        , _labelDetails = Nothing
        , _kind = Just CompletionItemKind_Variable
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

-- Document symbols
handleDocumentSymbols :: LspState -> TRequestMessage 'Method_TextDocumentDocumentSymbol -> (Either ResponseError (DocumentSymbol |? (SymbolInformation |? Null)) -> LspM () ()) -> LspM () ()
handleDocumentSymbols (LspState{..}) req responder = do
    let fileUri = req ^. params . textDocument . uri
        mFilePath = uriToFilePath fileUri
    
    case mFilePath of
        Just filePath -> do
            ws <- liftIO $ readTVarIO stateWorkspace
            case Map.lookup filePath (wsModules ws) of
                Just modState -> do
                    let symbols = extractDocumentSymbols (msAnalysis modState) fileUri
                    responder $ Right $ InL $ InL symbols
                Nothing -> responder $ Right $ InR $ InR Null
        Nothing -> responder $ Right $ InR $ InR Null

extractDocumentSymbols :: ModuleAnalysis -> Uri -> [DocumentSymbol]
extractDocumentSymbols ModuleAnalysis{..} fileUri =
    case maAst of
        Just (ExprRoot exprs) -> concatMap exprToSymbol exprs
        _ -> []
  where
    exprToSymbol :: Expr -> [DocumentSymbol]
    exprToSymbol (ExprBindingDef{..}) =
        [ DocumentSymbol
            { _name = T.pack bindingName
            , _detail = Nothing
            , _kind = SymbolKind_Function
            , _tags = Nothing
            , _deprecated = Nothing
            , _range = spanToRange bindingSpan
            , _selectionRange = spanToRange bindingSpan
            , _children = Nothing
            }
        ]
    exprToSymbol (ExprDataTypeDef{..}) =
        [ DocumentSymbol
            { _name = T.pack dataName
            , _detail = Nothing
            , _kind = SymbolKind_Class
            , _tags = Nothing
            , _deprecated = Nothing
            , _range = spanToRange dataSpan
            , _selectionRange = spanToRange dataSpan
            , _children = Just $ map constructorToSymbol dataConstructors
            }
        ]
    exprToSymbol (ExprTypeClassDef{..}) =
        [ DocumentSymbol
            { _name = T.pack typeClassName
            , _detail = Nothing
            , _kind = SymbolKind_Interface
            , _tags = Nothing
            , _deprecated = Nothing
            , _range = spanToRange typeClassSpan
            , _selectionRange = spanToRange typeClassSpan
            , _children = Nothing
            }
        ]
    exprToSymbol _ = []
    
    constructorToSymbol :: Expr -> DocumentSymbol
    constructorToSymbol (ExprDataConstructor{..}) =
        DocumentSymbol
            { _name = T.pack structConstructorName
            , _detail = Nothing
            , _kind = SymbolKind_Constructor
            , _tags = Nothing
            , _deprecated = Nothing
            , _range = spanToRange structConstructorSpan
            , _selectionRange = spanToRange structConstructorSpan
            , _children = Nothing
            }
    constructorToSymbol _ = Prelude.error "Invalid constructor"

-- Utility functions
parseErrorToDiagnostic :: String -> Diagnostic
parseErrorToDiagnostic err =
    Diagnostic
        { _range = Range (Position 0 0) (Position 0 0)
        , _severity = Just DiagnosticSeverity_Error
        , _code = Nothing
        , _codeDescription = Nothing
        , _source = Just "soma-parser"
        , _message = T.pack err
        , _tags = Nothing
        , _relatedInformation = Nothing
        , _data_ = Nothing
        }

analysisErrorToDiagnostic :: String -> FilePath -> String -> Diagnostic
analysisErrorToDiagnostic err _filePath _content =
    Diagnostic
        { _range = Range (Position 0 0) (Position 0 0)
        , _severity = Just DiagnosticSeverity_Error
        , _code = Nothing
        , _codeDescription = Nothing
        , _source = Just "soma-resolver"
        , _message = T.pack err
        , _tags = Nothing
        , _relatedInformation = Nothing
        , _data_ = Nothing
        }

inferenceErrorToDiagnostic :: String -> FilePath -> String -> Diagnostic
inferenceErrorToDiagnostic err _filePath _content =
    Diagnostic
        { _range = Range (Position 0 0) (Position 0 0)
        , _severity = Just DiagnosticSeverity_Error
        , _code = Nothing
        , _codeDescription = Nothing
        , _source = Just "soma-inference"
        , _message = T.pack err
        , _tags = Nothing
        , _relatedInformation = Nothing
        , _data_ = Nothing
        }

spanToRange :: Span -> Range
spanToRange (Span start end) =
    Range (positionToLspPosition start) (positionToLspPosition end)

positionToLspPosition :: Int -> Position
positionToLspPosition offset = Position 0 (fromIntegral offset)

filePathToUri :: FilePath -> Uri
filePathToUri path = Uri $ T.pack $ "file://" ++ path

listToMaybe :: [a] -> Maybe a
listToMaybe [] = Nothing
listToMaybe (x:_) = Just x
