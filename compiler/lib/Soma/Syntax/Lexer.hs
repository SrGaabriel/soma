{-# LANGUAGE NamedFieldPuns #-}

module Soma.Syntax.Lexer (LexerT, next, peek, runLexer, runLexerT) where

import Control.Monad.Identity
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import Data.Char (isNumber)
import qualified Data.Text as T
import Maple.Green (RawKind)
import Soma.Diagnostic (Diagnostic)
import Soma.Syntax.Kind
import Soma.Util (maybeM, safeIndex)
import Data.Text (Text)

data LexerState = LexerState
    { lxText :: T.Text
    , lxCursor :: Int
    }

type LexerT m = StateT LexerState (WriterT [Diagnostic] m)

data Token = Token {
    tKind :: !RawKind,
    tText :: Text
}

peekChar :: (Monad m) => LexerT m (Maybe Char)
peekChar = do
    (LexerState{lxText, lxCursor}) <- get
    pure $ safeIndex lxText lxCursor

bump :: (Monad m) => LexerT m (Maybe Char)
bump = do
    (LexerState{lxText, lxCursor}) <- get
    modify' (\s -> s{lxCursor = lxCursor + 1})
    pure $ safeIndex lxText lxCursor

bumpWhile :: (Monad m) => (Char -> Bool) -> LexerT m ()
bumpWhile f = do
    b <- peekChar
    case b of
        Just c | f c -> bump *> bumpWhile f
        _ -> pure ()

next :: (Monad m) => LexerT m RawKind
next = maybeM tEof lexChar (bump)

peek :: (Monad m) => LexerT m RawKind
peek = maybeM tEof lexChar (peekChar)

lexChar :: (Monad m) => Char -> LexerT m RawKind
lexChar '*' = pure tStar
lexChar c
    | isNumber c = lexNumber c
lexChar _ = pure tUnknown

lexNumber :: (Monad m) => Char -> LexerT m RawKind
lexNumber _leading = do
    _ <- bumpWhile isNumber
    pure tNumber

runLexerT :: (Monad m) => LexerState -> LexerT m a -> m (a, [Diagnostic])
runLexerT st lexer = do
    ((result, _), diag) <- runWriterT (runStateT lexer st)
    pure (result, diag)

runLexer :: LexerState -> LexerT Identity a -> (a, [Diagnostic])
runLexer st lexer =
    let ((result, _), diag) = runIdentity $ runWriterT (runStateT lexer st)
    in (result, diag)
