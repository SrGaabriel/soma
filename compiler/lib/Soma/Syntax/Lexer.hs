{-# LANGUAGE NamedFieldPuns #-}

module Soma.Syntax.Lexer where

import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Writer
import Data.Char (isNumber)
import qualified Data.Text as T
import Maple.Green (RawKind)
import Soma.Diagnostic (Diagnostic)
import Soma.Syntax.Kind
import Soma.Util (maybeM, safeIndex)

data LexerState = LexerState
    { lxText :: T.Text
    , lxCursor :: Int
    }

type LexerT m = StateT LexerState (WriterT [Diagnostic] m)

peek :: (Monad m) => LexerT m (Maybe Char)
peek = do
    (LexerState{lxText, lxCursor}) <- get
    pure $ safeIndex lxText lxCursor

bump :: (Monad m) => LexerT m (Maybe Char)
bump = do
    (LexerState{lxText, lxCursor}) <- get
    modify' (\s -> s{lxCursor = lxCursor + 1})
    pure $ safeIndex lxText lxCursor

bumpWhile :: (Monad m) => (Char -> Bool) -> LexerT m ()
bumpWhile f = do
    b <- peek
    case b of
        Just c | f c -> bump *> bumpWhile f
        _ -> pure ()

lex :: (Monad m) => LexerT m RawKind
lex = maybeM tEof lexChar (bump)

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
