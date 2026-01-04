{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}

module Souls.Handlers.Completion where

import Control.Concurrent.STM (readTVarIO)
import Control.Monad.IO.Class (liftIO)
import qualified Data.Map.Strict as Map
import Language.LSP.Protocol.Message (Method (..), TRequestMessage, TResponseError)
import Language.LSP.Protocol.Types
import Language.LSP.Server (LspM)
import Souls.Loc (extractReq)
import Souls.Server (LspState (..))
import Souls.Symbols (getCompletions)

handleCompletion ::
    LspState ->
    TRequestMessage 'Method_TextDocumentCompletion ->
    (Either (TResponseError 'Method_TextDocumentCompletion) ([CompletionItem] |? CompletionList |? Null) -> LspM () ()) ->
    LspM () ()
handleCompletion LspState{..} req responder = do
    let (_, fileUri) = extractReq req

    case uriToFilePath fileUri of
        Just filePath -> do
            compiled <- liftIO $ readTVarIO stateModules
            case Map.lookup filePath compiled of
                Just cm -> do
                    let completions = getCompletions cm compiled
                    responder $ Right $ InR (InL completions)
                Nothing -> do
                    responder $ Right $ InR (InL $ CompletionList False Nothing [])
        Nothing -> do
            responder $ Right $ InR (InL $ CompletionList False Nothing [])
