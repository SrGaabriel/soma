{-# LANGUAGE RecordWildCards #-}

module Souls.Analysis where

import Control.Concurrent.STM (modifyTVar)
import Control.Monad.IO.Class (liftIO)
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import GHC.Conc (atomically)
import GHC.Conc.Sync (readTVarIO)
import Language.LSP.Diagnostics
import Language.LSP.Protocol.Types
import Language.LSP.Server (LspM, getVirtualFile, publishDiagnostics)
import Language.LSP.VFS
import Lexing.Lexer (lexCode)
import Logging.Errors (PrintableError (..))
import Parsing.Ast (parse)
import Souls.Loc (offsetToPosition)
import Souls.Server (LspState (..), compileModuleForLSP)
import System.FilePath (dropExtension, takeFileName)

analyzeFile :: LspState -> Uri -> Int32 -> LspM () ()
analyzeFile LspState{..} fileUri fileVersion = do
    let nUri = toNormalizedUri fileUri
    mdoc <- getVirtualFile nUri

    case (mdoc, uriToFilePath fileUri) of
        (Just vf, Just filePath) -> do
            let content = virtualFileText vf
                modName = dropExtension $ takeFileName filePath
            let (tokens, lexErrors) = lexCode content
            let lexDiagnostics = map (errorToDiagnostic content) lexErrors

            case parse tokens of
                Left parseErrs -> do
                    let diags = map (errorToDiagnostic content) parseErrs ++ lexDiagnostics
                    publishDiagnostics 100 nUri Nothing (partitionBySource diags)
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
                        tyDiagnostics = map (errorToDiagnostic content) tyErrors
                        allDiagnostics = lexDiagnostics ++ parseDiagnostics ++ tyDiagnostics

                    liftIO
                        $ atomically
                        $ modifyTVar stateModules (Map.insert filePath compiled)

                    publishDiagnostics 100 nUri (Just fileVersion) (partitionBySource allDiagnostics)
        _ -> pure ()

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
