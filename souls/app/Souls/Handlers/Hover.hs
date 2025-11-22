{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}

module Souls.Handlers.Hover where

import Control.Concurrent.STM (readTVarIO)
import Control.Monad.IO.Class (liftIO)
import qualified Data.Map.Strict as Map
import Language.LSP.Protocol.Message (Method (..), TRequestMessage, TResponseError)
import Language.LSP.Protocol.Types
import Language.LSP.Server (LspM)
import Souls.Loc (extractReq)
import Souls.Server (LspState (..))
import Souls.Symbols (getHoverAt)

handleHover ::
    LspState ->
    TRequestMessage 'Method_TextDocumentHover ->
    (Either (TResponseError 'Method_TextDocumentHover) (Hover |? Null) -> LspM () ()) ->
    LspM () ()
handleHover LspState{..} req responder = do
    let (pos, fileUri) = extractReq req

    case uriToFilePath fileUri of
        Just filePath -> do
            compiled <- liftIO $ readTVarIO stateModules
            case Map.lookup filePath compiled of
                Just cm -> do
                    let mHover = getHoverAt pos cm
                    responder $ Right $ maybe (InR Null) InL mHover
                Nothing -> do
                    responder $ Right $ InR Null
        Nothing -> do
            responder $ Right $ InR Null
