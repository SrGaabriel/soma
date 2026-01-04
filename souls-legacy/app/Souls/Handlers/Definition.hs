{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}

module Souls.Handlers.Definition where

import Control.Concurrent.STM (readTVarIO)
import Control.Monad.IO.Class (liftIO)
import qualified Data.Map.Strict as Map
import Language.LSP.Protocol.Message (Method (..), TRequestMessage, TResponseError)
import Language.LSP.Protocol.Types
import Language.LSP.Server (LspM)
import Souls.Loc (extractReq)
import Souls.Server (LspState (..))
import Souls.Symbols (getDefinitionAt)

handleGotoDefinition ::
    LspState ->
    TRequestMessage 'Method_TextDocumentDefinition ->
    (Either (TResponseError 'Method_TextDocumentDefinition) (Definition |? [DefinitionLink] |? Null) -> LspM () ()) ->
    LspM () ()
handleGotoDefinition LspState{..} req responder = do
    let (pos, fileUri) = extractReq req

    case uriToFilePath fileUri of
        Just filePath -> do
            compiled <- liftIO $ readTVarIO stateModules
            case Map.lookup filePath compiled of
                Just cm -> do
                    let mLoc = getDefinitionAt pos cm compiled
                    responder
                        $ Right
                        $ maybe
                            (InR $ InR Null)
                            (InL . Definition . InL)
                            mLoc
                Nothing -> do
                    responder $ Right $ InR $ InR Null
        Nothing -> do
            responder $ Right $ InR $ InR Null
