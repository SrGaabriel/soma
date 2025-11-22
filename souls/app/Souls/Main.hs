{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Concurrent.STM
import Control.Lens ((^.))
import Control.Monad.IO.Class
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import qualified Language.LSP.Protocol.Lens as L
import Language.LSP.Protocol.Message
import Language.LSP.Protocol.Types
import Language.LSP.Server
import Project.Graph
import Souls.Analysis (analyzeFile)
import Souls.Handlers.Completion (handleCompletion)
import Souls.Handlers.Definition (handleGotoDefinition)
import Souls.Handlers.Hover (handleHover)
import Souls.Server (LspState (..))

main :: IO Int
main = do
    modulesVar <- newTVarIO Map.empty
    workspaceVar <- newTVarIO Nothing
    graphVar <- newTVarIO Nothing
    fileVersionsVar <- newTVarIO Map.empty

    let state = LspState modulesVar workspaceVar graphVar fileVersionsVar

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
            , Language.LSP.Server.options = defaultOptions
            }

handlers :: LspState -> ClientCapabilities -> Handlers (LspM ())
handlers state _caps =
    mconcat
        [ notificationHandler SMethod_Initialized $ \_msg ->
            sendNotification SMethod_WindowShowMessage
                $ ShowMessageParams MessageType_Info "Soma LSP initialized"
        , notificationHandler SMethod_TextDocumentDidOpen $ \msg -> do
            let fileUri = msg ^. L.params . L.textDocument . L.uri
            let fileVersion = msg ^. L.params . L.textDocument . L.version
            analyzeFile state fileUri fileVersion
        , notificationHandler SMethod_TextDocumentDidChange $ \msg -> do
            let fileUri = msg ^. L.params . L.textDocument . L.uri
            let fileVersion = msg ^. L.params . L.textDocument . L.version
            analyzeFile state fileUri fileVersion
        , requestHandler SMethod_TextDocumentHover (handleHover state)
        , requestHandler SMethod_TextDocumentDefinition (handleGotoDefinition state)
        , requestHandler SMethod_TextDocumentCompletion (handleCompletion state)
        ]
