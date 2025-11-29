{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Concurrent.STM
import Control.Lens ((^.))
import Control.Monad.IO.Class
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import qualified Language.LSP.Protocol.Lens as L
import Language.LSP.Protocol.Message
import Language.LSP.Protocol.Types hiding (
    DidChangeNotebookDocumentParams (..),
    NotebookDocumentSyncOptions (..),
    NotebookDocumentSyncRegistrationOptions (..),
    TextDocumentSyncClientCapabilities (..),
 )
import Language.LSP.Server
import Project.Graph
import Souls.Analysis (analyzeFile, reanalyzeFile)
import Souls.Handlers.Completion (handleCompletion)
import Souls.Handlers.Definition (handleGotoDefinition)
import Souls.Handlers.Hover (handleHover)
import Souls.Haoma (handleHaomaFileChange, watchHaomaFiles)
import Souls.Server (LspState (..))

main :: IO Int
main = do
    modulesVar <- newTVarIO Map.empty
    workspaceVar <- newTVarIO Nothing
    graphVar <- newTVarIO Nothing
    haomaProjectsVar <- newTVarIO Map.empty
    fileToProjectVar <- newTVarIO Map.empty
    openFilesVar <- newTVarIO Map.empty
    fileVersionsVar <- newTVarIO Map.empty

    let state = LspState modulesVar workspaceVar graphVar haomaProjectsVar fileToProjectVar openFilesVar fileVersionsVar

    runServer
        $ ServerDefinition
            { onConfigChange = const $ pure ()
            , defaultConfig = ()
            , configSection = T.pack "soma"
            , parseConfig = const $ const $ Right ()
            , doInitialize = \env req -> do
                let mRootUri = req ^. L.params . L.rootUri
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
            , Language.LSP.Server.options = lspOptions
            }

handlers :: LspState -> ClientCapabilities -> Handlers (LspM ())
handlers state _caps =
    mconcat
        [ notificationHandler SMethod_Initialized $ \_msg -> do
            watchHaomaFiles

            sendNotification SMethod_WindowShowMessage
                $ ShowMessageParams MessageType_Info "Soma LSP initialized"
        , notificationHandler SMethod_TextDocumentDidOpen $ \msg -> do
            let fileUri = msg ^. L.params . L.textDocument . L.uri
            let fileVersion = msg ^. L.params . L.textDocument . L.version
            case uriToFilePath fileUri of
                Just filePath -> do
                    liftIO $ atomically $ modifyTVar' (stateOpenFiles state) (Map.insert filePath fileUri)
                    analyzeFile state fileUri fileVersion
                Nothing -> pure ()
        , notificationHandler SMethod_TextDocumentDidClose $ \msg -> do
            let fileUri = msg ^. L.params . L.textDocument . L.uri
                filePathRes = uriToFilePath fileUri
            case filePathRes of
                Just filePath -> liftIO $ do
                    atomically $ do
                        modifyTVar' (stateModules state) (Map.delete filePath)
                        modifyTVar' (stateOpenFiles state) (Map.delete filePath)
                Nothing -> pure ()
        , notificationHandler SMethod_TextDocumentDidChange $ \msg -> do
            let fileUri = msg ^. L.params . L.textDocument . L.uri
            let fileVersion = msg ^. L.params . L.textDocument . L.version
            analyzeFile state fileUri fileVersion
        , requestHandler SMethod_TextDocumentHover (handleHover state)
        , requestHandler SMethod_TextDocumentDefinition (handleGotoDefinition state)
        , requestHandler SMethod_TextDocumentCompletion (handleCompletion state)
        , notificationHandler SMethod_WorkspaceDidChangeConfiguration $ \_msg ->
            pure ()
        , notificationHandler SMethod_WorkspaceDidChangeWatchedFiles $ \msg -> do
            let events = msg ^. L.params . L.changes
            handleHaomaFileChange
                (stateHaomaProjects state)
                (stateFileToProject state)
                (stateOpenFiles state)
                (reanalyzeFile state)
                events
        , notificationHandler SMethod_SetTrace $ \_msg ->
            pure ()
        ]

lspOptions :: Options
lspOptions =
    defaultOptions
        { optServerInfo = Just (ServerInfo "soma-lsp" (Just "0.1.0"))
        , optTextDocumentSync = syncOptions
        }

syncOptions :: Maybe TextDocumentSyncOptions
syncOptions =
    Just
        TextDocumentSyncOptions
            { _openClose = Just True
            , _change = Just TextDocumentSyncKind_Incremental
            , _willSave = Just False
            , _willSaveWaitUntil = Just False
            , _save = Just (InL False)
            }
