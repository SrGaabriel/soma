{-# LANGUAGE RecordWildCards #-}

module Souls.Analysis where

import Control.Concurrent.STM (TVar, modifyTVar, writeTVar)
import Control.Monad.IO.Class (liftIO)
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import Format.Errors (PrintableError (..))
import GHC.Conc (atomically)
import GHC.Conc.Sync (readTVarIO)
import Language.LSP.Diagnostics
import Language.LSP.Protocol.Types
import Language.LSP.Server (LspM, getVirtualFile, publishDiagnostics)
import Language.LSP.VFS
import Lexing.Lexer (lexCode)
import Parsing.Ast (parse)
import Souls.Haoma (HaomaProject, findHaomaProject, loadExternalDeps)
import Souls.Loc (offsetToPosition)
import Souls.Server (ExternalDeps (..), LspState (..), compileModuleForLSP, emptyExternalDeps)
import System.FilePath (dropExtension, takeFileName)

analyzeFile :: LspState -> Uri -> Int32 -> LspM () ()
analyzeFile LspState{..} fileUri fileVersion = do
    let nUri = toNormalizedUri fileUri
    mdoc <- getVirtualFile nUri

    case (mdoc, uriToFilePath fileUri) of
        (Just vf, Just filePath) -> do
            extDeps <- liftIO $ ensureExternalDeps filePath stateHaomaProject stateExternalDeps

            let content = virtualFileText vf
                modName = dropExtension $ takeFileName filePath
            let (tokens, lexErrors) = lexCode content
            let lexDiagnostics = map (errorToDiagnostic content) lexErrors

            case parse tokens of
                Left parseErrs -> do
                    let diags = map (errorToDiagnostic content) parseErrs ++ lexDiagnostics
                    publishDiagnostics 100 nUri (Just fileVersion) (partitionBySource diags)
                Right (parseErrors, ast) -> do
                    let parseDiagnostics = map (errorToDiagnostic content) parseErrors
                    compiledMods <- liftIO $ readTVarIO stateModules
                    let depsOnly = Map.delete filePath compiledMods
                        (tyErrors, compiled) =
                            compileModuleForLSP
                                modName
                                filePath
                                (T.unpack content)
                                ast
                                depsOnly
                                extDeps
                        tyDiagnostics = map (errorToDiagnostic content) tyErrors
                        allDiagnostics = lexDiagnostics ++ parseDiagnostics ++ tyDiagnostics

                    liftIO
                        $ atomically
                        $ modifyTVar stateModules (Map.insert filePath compiled)

                    publishDiagnostics 100 nUri (Just fileVersion) (partitionBySource allDiagnostics)
        _ -> pure ()

ensureExternalDeps ::
    FilePath ->
    TVar (Maybe HaomaProject) ->
    TVar ExternalDeps ->
    IO ExternalDeps
ensureExternalDeps filePath haomaProjectVar externalDepsVar = do
    cachedProject <- readTVarIO haomaProjectVar
    cachedDeps <- readTVarIO externalDepsVar

    case cachedProject of
        Just _ ->
            return cachedDeps
        Nothing -> do
            mProject <- findHaomaProject filePath
            case mProject of
                Nothing ->
                    return emptyExternalDeps
                Just project -> do
                    result <- loadExternalDeps project
                    case result of
                        Left _err ->
                            return emptyExternalDeps
                        Right (types, instances) -> do
                            let extDeps = ExternalDeps types instances
                            atomically $ do
                                writeTVar haomaProjectVar (Just project)
                                writeTVar externalDepsVar extDeps
                            return extDeps

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
        , _source = Just $ T.pack "soma"
        , _message = T.pack $ errorMessage err
        , _tags = Nothing
        , _relatedInformation = Nothing
        , _data_ = Nothing
        }
