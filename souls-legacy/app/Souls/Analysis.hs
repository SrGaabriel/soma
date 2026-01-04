{-# LANGUAGE RecordWildCards #-}

module Souls.Analysis (analyzeFile, reanalyzeFile) where

import Control.Concurrent.STM (TVar, modifyTVar, modifyTVar')
import Control.Monad.IO.Class (liftIO)
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import Format.Errors (PrintableError (..))
import GHC.Conc (atomically)
import GHC.Conc.Sync (readTVarIO)
import Language.LSP.Diagnostics
import Language.LSP.Protocol.Types
import Language.LSP.Server (LspM, getVirtualFile, publishDiagnostics)
import Language.LSP.VFS (virtualFileText)
import Lexing.Lexer (lexCode)
import Parsing.Ast (parse)
import Souls.Haoma (ExternalDeps (..), HaomaProject (..), HaomaProjectCache (..), emptyExternalDeps, findHaomaProject, loadExternalDeps)
import Souls.Loc (offsetToPosition)
import Souls.Server (LspState (..), compileModuleForLSP)
import System.FilePath (dropExtension, takeFileName)

reanalyzeFile :: LspState -> Uri -> LspM () ()
reanalyzeFile = reanalyzeFileInternal

analyzeFile :: LspState -> Uri -> Int32 -> LspM () ()
analyzeFile state fileUri fileVersion = analyzeFileWithVersion state fileUri (Just fileVersion)

reanalyzeFileInternal :: LspState -> Uri -> LspM () ()
reanalyzeFileInternal state fileUri = analyzeFileWithVersion state fileUri Nothing

analyzeFileWithVersion :: LspState -> Uri -> Maybe Int32 -> LspM () ()
analyzeFileWithVersion LspState{..} fileUri fileVersion = do
    let nUri = toNormalizedUri fileUri
    mdoc <- getVirtualFile nUri

    case (mdoc, uriToFilePath fileUri) of
        (Just vf, Just filePath) -> do
            extDeps <- liftIO $ ensureExternalDeps filePath stateHaomaProjects stateFileToProject

            let content = virtualFileText vf
                modName = dropExtension $ takeFileName filePath

            version <- case fileVersion of
                Just v -> do
                    liftIO $ atomically $ modifyTVar' stateFileVersions (Map.insert filePath v)
                    return $ Just v
                Nothing -> do
                    lastVersion <- liftIO $ readTVarIO stateFileVersions
                    let currentVersion = Map.findWithDefault 0 filePath lastVersion
                        newVersion = currentVersion + 1
                    liftIO $ atomically $ modifyTVar' stateFileVersions (Map.insert filePath newVersion)
                    return $ Just newVersion

            let (tokens, lexErrors) = lexCode content
            let lexDiagnostics = map (errorToDiagnostic content) lexErrors

            case parse tokens of
                Left parseErrs -> do
                    let diags = map (errorToDiagnostic content) parseErrs ++ lexDiagnostics
                    publishDiagnostics 100 nUri version (partitionBySource diags)
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

                    publishDiagnostics 100 nUri version (partitionBySource allDiagnostics)
        _ -> pure ()

ensureExternalDeps ::
    FilePath ->
    TVar (Map.Map FilePath HaomaProjectCache) ->
    TVar (Map.Map FilePath FilePath) ->
    IO ExternalDeps
ensureExternalDeps filePath haomaProjectsVar fileToProjectVar = do
    fileToProject <- readTVarIO fileToProjectVar
    case Map.lookup filePath fileToProject of
        Just projectRoot -> do
            projects <- readTVarIO haomaProjectsVar
            case Map.lookup projectRoot projects of
                Just cached -> return (hpcExternalDeps cached)
                Nothing -> loadAndCacheProject filePath haomaProjectsVar fileToProjectVar
        Nothing -> loadAndCacheProject filePath haomaProjectsVar fileToProjectVar

loadAndCacheProject ::
    FilePath ->
    TVar (Map.Map FilePath HaomaProjectCache) ->
    TVar (Map.Map FilePath FilePath) ->
    IO ExternalDeps
loadAndCacheProject filePath haomaProjectsVar fileToProjectVar = do
    mProject <- findHaomaProject filePath
    case mProject of
        Nothing -> return emptyExternalDeps
        Just project -> do
            let projectRoot = hpRoot project
            result <- loadExternalDeps project
            case result of
                Left _err -> return emptyExternalDeps
                Right (types, instances) -> do
                    let extDeps = ExternalDeps types instances
                        cache = HaomaProjectCache project extDeps
                    atomically $ do
                        modifyTVar' haomaProjectsVar (Map.insert projectRoot cache)
                        modifyTVar' fileToProjectVar (Map.insert filePath projectRoot)
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
