{-# LANGUAGE RecordWildCards #-}
module Souls.Analysis where
import Souls.Server (LspState (..), compileModuleForLSP)
import Language.LSP.Protocol.Types
import Language.LSP.Server (LspM, publishDiagnostics, getVirtualFile)
import Language.LSP.Diagnostics
import qualified Data.Text as T
import Souls.Loc (offsetToPosition)
import Logging.Errors (PrintableError(..))
import Language.LSP.VFS
import System.FilePath (dropExtension, takeFileName)
import Lexing.Lexer (lexCode)
import Parsing.Ast (parse)
import Control.Monad.IO.Class (liftIO)
import GHC.Conc.Sync (readTVarIO)
import GHC.Conc (atomically)
import Control.Concurrent.STM (modifyTVar)
import qualified Data.Map.Strict as Map

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
                    publishDiagnostics 100 nUri Nothing (partitionBySource diags)
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
                            publishDiagnostics 100 nUri Nothing (partitionBySource diags)
                        Right compiled -> do
                            liftIO
                                $ atomically
                                $ modifyTVar stateModules (Map.insert filePath compiled)
                            publishDiagnostics 100 nUri Nothing (partitionBySource [])
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