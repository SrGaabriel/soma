{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

module Main where

import Control.Applicative.Combinators (skipManyTill)
import Control.Concurrent (threadDelay)
import Control.Lens hiding (List)
import Control.Monad.IO.Class
import Data.Default (def)
import Data.List (isInfixOf, length)
import qualified Data.Text as T
import Language.LSP.Protocol.Lens hiding (length, message)
import qualified Language.LSP.Protocol.Lens as L
import Language.LSP.Protocol.Message (SMethod (..), TResponseMessage (..))
import Language.LSP.Protocol.Types
import Language.LSP.Test
import System.Directory (makeAbsolute)
import Test.Hspec
import Prelude hiding (length)

lspCmd :: String
lspCmd = "souls"

main :: IO ()
main = do
    hspec $ do
        describe "SouLS (Soma Language Server) LSP Tests" $ do
            testInitialization
            testDiagnostics
            testHover
            testGotoDefinition
            testCompletion
            testHaomaProjects

mkConfig :: String -> SessionConfig
mkConfig _cmd =
    def
        { messageTimeout = 30
        , logStdErr = True
        , logMessages = True
        , logColor = True
        , ignoreRegistrationRequests = False
        }

testInitialization :: Spec
testInitialization = describe "Initialization" $ do
    it "should initialize and open a document"
        $ runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures"
        $ do
            _doc <- openDoc "valid.soma" "soma"
            -- just verify we can open a document without errors
            return ()

testDiagnostics :: Spec
testDiagnostics = describe "Diagnostics" $ do
    it "should report parse errors"
        $ runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures"
        $ do
            _doc <- openDoc "parse_error.soma" "soma"
            diags <- waitForDiagnostics
            liftIO $ length diags `shouldSatisfy` (> 0)

            let firstDiag = head diags
            liftIO $ firstDiag ^. severity `shouldBe` Just DiagnosticSeverity_Error
            liftIO $ (T.unpack <$> firstDiag ^. source) `shouldBe` Just "soma"

    it "should report type errors"
        $ runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures"
        $ do
            _doc <- openDoc "type_error.soma" "soma"
            diags <- waitForDiagnostics
            liftIO $ length diags `shouldSatisfy` (> 0)

    it "should clear diagnostics on fix"
        $ runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures"
        $ do
            doc <- openDoc "fixable.soma" "soma"
            _ <- waitForDiagnostics

            changeDoc doc [TextDocumentContentChangeEvent $ InR $ TextDocumentContentChangeWholeDocument "def x :: String = \"oops\"\n"]

            diags <- waitForDiagnostics
            liftIO $ diags `shouldBe` []

    it "should handle valid files without errors"
        $ runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures"
        $ do
            _doc <- openDoc "valid.soma" "soma"
            diags <- waitForDiagnosticsFrom "soma"
            liftIO $ diags `shouldBe` []

testHover :: Spec
testHover = describe "Hover" $ do
    it "should show type information on hover"
        $ runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures"
        $ do
            doc <- openDoc "valid.soma" "soma"
            hover' <- getHover doc (Position 2 5)

            case hover' of
                Just (Hover (InL content) _) -> do
                    liftIO $ content ^. kind `shouldBe` MarkupKind_Markdown
                    liftIO $ T.unpack (content ^. value) `shouldContain` "```soma"
                _ -> liftIO $ expectationFailure "Expected hover content"

    it "should return null for invalid positions"
        $ runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures"
        $ do
            doc <- openDoc "valid.soma" "soma"
            hover' <- getHover doc (Position 100 100)
            liftIO $ hover' `shouldBe` Nothing

    it "should show type for expressions"
        $ runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures"
        $ do
            doc <- openDoc "expression.soma" "soma"
            hover' <- getHover doc (Position 3 10)

            liftIO
                $ hover' `shouldSatisfy` \case
                    Just (Hover (InL _) _) -> True
                    _ -> False

testGotoDefinition :: Spec
testGotoDefinition = describe "Go to Definition" $ do
    it "should navigate to local definition"
        $ runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures"
        $ do
            doc <- openDoc "valid.soma" "soma"
            defs <- getDefinitions doc (Position 11 25)

            case defs of
                InL defn -> do
                    let (Definition locOrLocs) = defn
                    case locOrLocs of
                        InL loc ->
                            liftIO $ loc ^. range . L.start . L.line `shouldSatisfy` (>= 0)
                        InR locs ->
                            liftIO $ length locs `shouldSatisfy` (> 0)
                InR (InL _links) -> liftIO $ expectationFailure "Got definition links instead of locations"
                InR (InR Null) -> liftIO $ expectationFailure "Expected definition"

    it "should navigate to imported definition"
        $ runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures"
        $ do
            _doc1 <- openDoc "module1.soma" "soma"
            doc <- openDoc "with_imports.soma" "soma"
            defs <- getDefinitions doc (Position 2 25)

            case defs of
                InL defn -> do
                    let (Definition locOrLocs) = defn
                    case locOrLocs of
                        InL _loc -> return ()
                        InR locs -> liftIO $ length locs `shouldSatisfy` (> 0)
                InR (InL _links) -> return ()
                InR (InR Null) -> liftIO $ expectationFailure "Expected definition"

    it "should return null for undefined symbols"
        $ runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures"
        $ do
            doc <- openDoc "valid.soma" "soma"
            defs <- getDefinitions doc (Position 0 0)

            case defs of
                InR (InR Null) -> return ()
                _ -> liftIO $ expectationFailure "Expected null"

    it "should handle cross-file definitions"
        $ runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures"
        $ do
            _doc1 <- openDoc "module1.soma" "soma"
            doc2 <- openDoc "module2.soma" "soma"
            defs <- getDefinitions doc2 (Position 2 25)

            case defs of
                InL defn -> do
                    let (Definition locOrLocs) = defn
                    case locOrLocs of
                        InL loc -> do
                            let locUri = loc ^. L.uri
                            liftIO
                                $ uriToFilePath locUri
                                    `shouldSatisfy` \case
                                        Just path -> "module1.soma" `isInfixOf` path
                                        Nothing -> False
                        InR (loc : _) -> do
                            let locUri = loc ^. L.uri
                            liftIO
                                $ uriToFilePath locUri
                                    `shouldSatisfy` \case
                                        Just path -> "module1.soma" `isInfixOf` path
                                        Nothing -> False
                        InR [] -> liftIO $ expectationFailure "Expected at least one location"
                InR (InL _links) -> return ()
                InR (InR Null) -> liftIO $ expectationFailure "Expected cross-file location"

testCompletion :: Spec
testCompletion = describe "Completion" $ do
    it "should provide completions for local symbols"
        $ runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures"
        $ do
            doc <- openDoc "valid.soma" "soma"
            items' <- getCompletions doc (Position 6 0)

            liftIO $ length items' `shouldSatisfy` (> 0)
            liftIO
                $ map (^. label) items'
                    `shouldSatisfy` \labels -> any (\l -> T.length l > 0) labels

    it "should include imported symbols"
        $ runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures"
        $ do
            doc <- openDoc "with_imports.soma" "soma"
            items' <- getCompletions doc (Position 5 0)
            liftIO $ length items' `shouldSatisfy` (> 0)

    it "should provide function completions"
        $ runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures"
        $ do
            doc <- openDoc "valid.soma" "soma"
            items' <- getCompletions doc (Position 4 2)

            liftIO
                $ any (\item' -> item' ^. kind == Just CompletionItemKind_Function) items'
                    `shouldBe` True

    it "should handle completion in empty context"
        $ runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures"
        $ do
            doc <- openDoc "empty.soma" "soma"
            _items <- getCompletions doc (Position 0 0)

            return ()

testHaomaProjects :: Spec
testHaomaProjects = describe "Haoma Project Integration" $ do
    it "should handle files in a haoma library project"
        $ runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures/haoma_project/mylib"
        $ do
            _doc <- openDoc "src/core.soma" "soma"
            diags <- waitForDiagnosticsFrom "soma"
            liftIO $ diags `shouldBe` []

    it "should resolve cross-package imports without errors"
        $ runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures/haoma_project/myapp"
        $ do
            _doc <- openDoc "src/main.soma" "soma"
            diags <- waitForDiagnosticsFrom "soma"
            liftIO $ diags `shouldBe` []

    it "should provide hover for cross-package imported symbols"
        $ runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures/haoma_project/myapp"
        $ do
            _doc <- openDoc "src/main.soma" "soma"
            _ <- waitForDiagnostics
            hover' <- getHover _doc (Position 2 18)
            liftIO
                $ hover' `shouldSatisfy` \case
                    Just (Hover (InL content) _) ->
                        "Int" `T.isInfixOf` (content ^. value)
                    _ -> False

    it "should resolve imports from external modules that have intra-package dependencies"
        $ runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures/haoma_project/deepapp"
        $ do
            _doc <- openDoc "src/main.soma" "soma"
            diags <- waitForDiagnosticsFrom "soma"
            liftIO $ diags `shouldBe` []

    it "should resolve transitive package dependencies (A depends on B depends on C)"
        $ runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures/haoma_project/topapp"
        $ do
            _doc <- openDoc "src/main.soma" "soma"
            diags <- waitForDiagnosticsFrom "soma"
            liftIO $ diags `shouldBe` []

    it "should resolve transitive deps when alphabetical order differs from dependency order"
        $ runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures/haoma_project/mmtop"
        $ do
            _doc <- openDoc "src/main.soma" "soma"
            diags <- waitForDiagnosticsFrom "soma"
            liftIO $ diags `shouldBe` []

    it "should report parse errors in haoma projects"
        $ runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures/haoma_project/broken"
        $ do
            _doc <- openDoc "src/main.soma" "soma"
            diags <- waitForDiagnostics
            liftIO $ length diags `shouldSatisfy` (> 0)
            let firstDiag = head diags
            liftIO $ firstDiag ^. severity `shouldBe` Just DiagnosticSeverity_Error

    it "should reload deps and clear diagnostics when haoma.toml dependency added"
        $ do
            liftIO
                $ writeFile
                    "test/fixtures/haoma_project/dynapp/haoma.toml"
                    "name = \"dynapp\"\nversion = \"0.1.0\"\ntype = \"binary\"\n\n[dependencies]\n"

            runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures/haoma_project/dynapp"
                $ do
                    doc <- openDoc "src/main.soma" "soma"

                    skipManyTill anyMessage $ do
                        req <- message SMethod_ClientRegisterCapability
                        let rspId = req ^. L.id
                        sendResponse $ TResponseMessage "2.0" (Just rspId) (Right Null)

                    liftIO $ threadDelay 100000 -- 100ms
                    diags1 <- waitForDiagnosticsFrom "soma"
                    liftIO $ length diags1 `shouldSatisfy` (> 0)

                    liftIO
                        $ writeFile
                            "test/fixtures/haoma_project/dynapp/haoma.toml"
                            "name = \"dynapp\"\nversion = \"0.1.0\"\ntype = \"binary\"\n\n[dependencies]\nmylib = { path = \"../mylib\" }\n"

                    liftIO $ threadDelay 100000 -- 100ms
                    haomaAbsPath <- liftIO $ makeAbsolute "test/fixtures/haoma_project/dynapp/haoma.toml"
                    let haomaUri = Uri $ T.pack $ "file://" ++ haomaAbsPath
                        changeEvent = FileEvent haomaUri FileChangeType_Changed
                        fileParams = DidChangeWatchedFilesParams [changeEvent]
                    sendNotification SMethod_WorkspaceDidChangeWatchedFiles fileParams

                    diags2 <- waitForDiagnosticsFrom "soma"
                    liftIO $ diags2 `shouldBe` []

                    closeDoc doc

            liftIO
                $ writeFile
                    "test/fixtures/haoma_project/dynapp/haoma.toml"
                    "name = \"dynapp\"\nversion = \"0.1.0\"\ntype = \"binary\"\n\n[dependencies]\n"
    it "should break, reload deps and clear diagnostics when haoma.toml dependency added"
        $ do
            liftIO
                $ writeFile
                    "test/fixtures/haoma_project/dynapp2/haoma.toml"
                    "name = \"dynapp2\"\nversion = \"0.1.0\"\ntype = \"binary\"\n\n[dependencies]\nmylib = { path = \"../mylib\" }\n"

            runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures/haoma_project/dynapp2"
                $ do
                    doc <- openDoc "src/main.soma" "soma"

                    skipManyTill anyMessage $ do
                        req <- message SMethod_ClientRegisterCapability
                        let rspId = req ^. L.id
                        sendResponse $ TResponseMessage "2.0" (Just rspId) (Right Null)

                    liftIO $ threadDelay 100000 -- 100ms
                    diags1 <- waitForDiagnosticsFrom "soma"
                    liftIO $ diags1 `shouldBe` []

                    liftIO
                        $ writeFile
                            "test/fixtures/haoma_project/dynapp2/haoma.toml"
                            "name = \"dynapp2\"\nversion = \"0.1.0\"\ntype = \"binary\"\n\n[dependencies]\n"

                    liftIO $ threadDelay 100000 -- 100ms
                    haomaAbsPath' <- liftIO $ makeAbsolute "test/fixtures/haoma_project/dynapp2/haoma.toml"
                    let haomaUri' = Uri $ T.pack $ "file://" ++ haomaAbsPath'
                        changeEvent' = FileEvent haomaUri' FileChangeType_Changed
                        fileParams' = DidChangeWatchedFilesParams [changeEvent']
                    sendNotification SMethod_WorkspaceDidChangeWatchedFiles fileParams'

                    diags2 <- waitForDiagnosticsFrom "soma"
                    liftIO $ length diags2 `shouldSatisfy` (> 0)

                    liftIO
                        $ writeFile
                            "test/fixtures/haoma_project/dynapp2/haoma.toml"
                            "name = \"dynapp2\"\nversion = \"0.1.0\"\ntype = \"binary\"\n\n[dependencies]\nmylib = { path = \"../mylib\" }\n"

                    liftIO $ threadDelay 100000 -- 100ms
                    haomaAbsPath <- liftIO $ makeAbsolute "test/fixtures/haoma_project/dynapp2/haoma.toml"
                    let haomaUri = Uri $ T.pack $ "file://" ++ haomaAbsPath
                        changeEvent = FileEvent haomaUri FileChangeType_Changed
                        fileParams = DidChangeWatchedFilesParams [changeEvent]
                    sendNotification SMethod_WorkspaceDidChangeWatchedFiles fileParams

                    diags3 <- waitForDiagnosticsFrom "soma"
                    liftIO $ diags3 `shouldBe` []

                    closeDoc doc

    it "should handle haoma.toml changes after document edits"
        $ do
            liftIO
                $ writeFile
                    "test/fixtures/haoma_project/dynapp2/haoma.toml"
                    "name = \"dynapp2\"\nversion = \"0.1.0\"\ntype = \"binary\"\n\n[dependencies]\nmylib = { path = \"../mylib\" }\n"

            runSessionWithConfig (mkConfig lspCmd) lspCmd fullCaps "test/fixtures/haoma_project/dynapp2"
                $ do
                    doc <- openDoc "src/main.soma" "soma"

                    skipManyTill anyMessage $ do
                        req <- message SMethod_ClientRegisterCapability
                        let rspId = req ^. L.id
                        sendResponse $ TResponseMessage "2.0" (Just rspId) (Right Null)

                    liftIO $ threadDelay 100000 -- 100ms
                    diags1 <- waitForDiagnosticsFrom "soma"
                    liftIO $ diags1 `shouldBe` []

                    -- Make several document edits to increment the version
                    changeDoc doc [TextDocumentContentChangeEvent $ InR $ TextDocumentContentChangeWholeDocument "use mylib.{add}\n\ndef main :: Int = add 1 2\n"]
                    _ <- waitForDiagnosticsFrom "soma"

                    changeDoc doc [TextDocumentContentChangeEvent $ InR $ TextDocumentContentChangeWholeDocument "use mylib.{add}\n\ndef main :: Int = add 2 3\n"]
                    _ <- waitForDiagnosticsFrom "soma"

                    changeDoc doc [TextDocumentContentChangeEvent $ InR $ TextDocumentContentChangeWholeDocument "use mylib.{add}\n\ndef main :: Int = add 3 4\n"]
                    diags2 <- waitForDiagnosticsFrom "soma"
                    liftIO $ diags2 `shouldBe` []

                    liftIO
                        $ writeFile
                            "test/fixtures/haoma_project/dynapp2/haoma.toml"
                            "name = \"dynapp2\"\nversion = \"0.1.0\"\ntype = \"binary\"\n\n[dependencies]\n"

                    liftIO $ threadDelay 100000 -- 100ms
                    haomaAbsPath <- liftIO $ makeAbsolute "test/fixtures/haoma_project/dynapp2/haoma.toml"
                    let haomaUri = Uri $ T.pack $ "file://" ++ haomaAbsPath
                        changeEvent = FileEvent haomaUri FileChangeType_Changed
                        fileParams = DidChangeWatchedFilesParams [changeEvent]
                    sendNotification SMethod_WorkspaceDidChangeWatchedFiles fileParams

                    diags3 <- waitForDiagnosticsFrom "soma"
                    liftIO $ length diags3 `shouldSatisfy` (> 0)

                    liftIO
                        $ writeFile
                            "test/fixtures/haoma_project/dynapp2/haoma.toml"
                            "name = \"dynapp2\"\nversion = \"0.1.0\"\ntype = \"binary\"\n\n[dependencies]\nmylib = { path = \"../mylib\" }\n"

                    liftIO $ threadDelay 100000 -- 100ms
                    let changeEvent' = FileEvent haomaUri FileChangeType_Changed
                        fileParams' = DidChangeWatchedFilesParams [changeEvent']
                    sendNotification SMethod_WorkspaceDidChangeWatchedFiles fileParams'

                    diags4 <- waitForDiagnosticsFrom "soma"
                    liftIO $ diags4 `shouldBe` []

                    closeDoc doc

waitForDiagnosticsFrom :: T.Text -> Session [Diagnostic]
waitForDiagnosticsFrom src = do
    filter (\d -> d ^. source == Just src) <$> waitForDiagnostics

fullCaps :: ClientCapabilities
fullCaps =
    ClientCapabilities
        { _textDocument =
            Just
                $ TextDocumentClientCapabilities
                    { _synchronization =
                        Just
                            $ TextDocumentSyncClientCapabilities
                                { _dynamicRegistration = Just True
                                , _willSave = Just True
                                , _willSaveWaitUntil = Just True
                                , _didSave = Just True
                                }
                    , _completion =
                        Just
                            $ CompletionClientCapabilities
                                { _dynamicRegistration = Just True
                                , _completionItem =
                                    Just
                                        $ ClientCompletionItemOptions
                                            { _snippetSupport = Just True
                                            , _commitCharactersSupport = Just True
                                            , _documentationFormat = Just [MarkupKind_Markdown, MarkupKind_PlainText]
                                            , _deprecatedSupport = Just True
                                            , _preselectSupport = Just True
                                            , _tagSupport = Nothing
                                            , _insertReplaceSupport = Nothing
                                            , _resolveSupport = Nothing
                                            , _insertTextModeSupport = Nothing
                                            , _labelDetailsSupport = Nothing
                                            }
                                , _completionItemKind = Nothing
                                , _contextSupport = Nothing
                                , _insertTextMode = Nothing
                                , _completionList = Nothing
                                }
                    , _hover =
                        Just
                            $ HoverClientCapabilities
                                { _dynamicRegistration = Just True
                                , _contentFormat = Just [MarkupKind_Markdown, MarkupKind_PlainText]
                                }
                    , _definition =
                        Just
                            $ DefinitionClientCapabilities
                                { _dynamicRegistration = Just True
                                , _linkSupport = Just True
                                }
                    , _signatureHelp = Nothing
                    , _references = Nothing
                    , _documentHighlight = Nothing
                    , _documentSymbol = Nothing
                    , _formatting = Nothing
                    , _rangeFormatting = Nothing
                    , _onTypeFormatting = Nothing
                    , _declaration = Nothing
                    , _typeDefinition = Nothing
                    , _implementation = Nothing
                    , _codeAction = Nothing
                    , _codeLens = Nothing
                    , _documentLink = Nothing
                    , _colorProvider = Nothing
                    , _rename = Nothing
                    , _publishDiagnostics = Nothing
                    , _foldingRange = Nothing
                    , _selectionRange = Nothing
                    , _linkedEditingRange = Nothing
                    , _callHierarchy = Nothing
                    , _semanticTokens = Nothing
                    , _moniker = Nothing
                    , _typeHierarchy = Nothing
                    , _inlineValue = Nothing
                    , _inlayHint = Nothing
                    , _diagnostic = Nothing
                    }
        , _workspace =
            Just
                $ WorkspaceClientCapabilities
                    { _applyEdit = Just True
                    , _workspaceEdit = Nothing
                    , _didChangeConfiguration = Nothing
                    , _didChangeWatchedFiles = Just $ DidChangeWatchedFilesClientCapabilities (Just True) (Just True)
                    , _symbol = Nothing
                    , _executeCommand = Nothing
                    , _workspaceFolders = Just True
                    , _configuration = Just False
                    , _semanticTokens = Nothing
                    , _codeLens = Nothing
                    , _fileOperations = Nothing
                    , _inlineValue = Nothing
                    , _inlayHint = Nothing
                    , _diagnostics = Nothing
                    }
        , _window = Nothing
        , _general = Nothing
        , _notebookDocument = Nothing
        , _experimental = Nothing
        }
