{-# LANGUAGE NamedFieldPuns #-}

module Soma.Syntax.Lexer where

import Control.Monad.State
import Control.Monad.Writer
import Data.Text (Text)
import qualified Data.Text as T
import Soma.Diagnostic (Diagnostic)
import Maple.Green (RawKind)

data LexerState = LexerState
    { lxText :: Text
    , lxCursor :: Int
    }

type LexerT m = StateT LexerState (WriterT [Diagnostic] m)

next :: (Monad m) => LexerT m Char
next = do
    (LexerState{lxText, lxCursor}) <- get
    pure $ T.index lxText lxCursor

