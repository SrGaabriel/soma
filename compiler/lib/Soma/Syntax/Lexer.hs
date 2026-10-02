{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

module Soma.Syntax.Lexer (
    LexerT,
    LexerState,
    Token (..),
    mkLexerState,
    next,
    peek,
    peekNth,
    runLexer,
    runLexerT,
    lexAll,
) where

import Control.Monad.Identity
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import Data.Char (isAlpha, isAlphaNum, isNumber)
import Data.Sequence (Seq (..), (|>))
import Data.Sequence qualified as Seq
import Data.Text (Text)
import Data.Text qualified as T
import Maple.Green (RawKind)
import Soma.Diagnostic (Diagnostic)
import Soma.Syntax.Kind
import Soma.Util (maybeM)

data LexerState = LexerState
    { lxRest :: !Text
    , lxCursor :: !Int
    , lxBuffer :: !(Seq Token)
    }

mkLexerState :: Text -> LexerState
mkLexerState txt = LexerState{lxRest = txt, lxCursor = 0, lxBuffer = Seq.empty}

type LexerT m = StateT LexerState (WriterT [Diagnostic] m)

data Token = Token
    { tKind :: !RawKind
    , tText :: Text
    }
    deriving (Show, Eq)

next :: (Monad m) => LexerT m Token
next = do
    buf <- gets lxBuffer
    case buf of
        t :<| rest -> t <$ modify' (\s -> s{lxBuffer = rest})
        Empty -> lexToken

peek :: (Monad m) => LexerT m Token
peek = peekNth 0

peekNth :: (Monad m) => Int -> LexerT m Token
peekNth n = do
    buf <- gets lxBuffer
    case Seq.lookup n buf of
        Just t -> pure t
        Nothing -> do
            t <- lexToken
            modify' (\s -> s{lxBuffer = lxBuffer s |> t})
            peekNth n

peekChar :: (Monad m) => LexerT m (Maybe Char)
peekChar = gets (fmap fst . T.uncons . lxRest)

bumpChar :: (Monad m) => LexerT m (Maybe Char)
bumpChar = do
    LexerState{lxRest, lxCursor} <- get
    case T.uncons lxRest of
        Just (c, rest) -> do
            modify' (\s -> s{lxRest = rest, lxCursor = lxCursor + 1})
            pure (Just c)
        Nothing -> pure Nothing

bumpWhile :: (Monad m) => (Char -> Bool) -> LexerT m Text
bumpWhile f = do
    LexerState{lxRest, lxCursor} <- get
    let (taken, rest) = T.span f lxRest
    modify' (\s -> s{lxRest = rest, lxCursor = lxCursor + T.length taken})
    pure taken

emptyToken :: RawKind -> Token
emptyToken k = Token k T.empty

charToken :: RawKind -> Char -> Token
charToken k c = Token k $ T.singleton c

eofToken :: Token
eofToken = emptyToken kEof

unknownToken :: Text -> Token
unknownToken text = Token kUnknown text

lexToken :: (Monad m) => LexerT m Token
lexToken = maybeM eofToken lexChar peekChar

lexChar :: (Monad m) => Char -> LexerT m Token
lexChar c@'*' = charToken kStar c <$ bumpChar
lexChar c
    | isNumber c = lexNumber
    | isAlpha c = lexWord
lexChar c = unknownToken (T.singleton c) <$ bumpChar

lexNumber :: (Monad m) => LexerT m Token
lexNumber = Token kNumber <$> bumpWhile isNumber

lexWord :: (Monad m) => LexerT m Token
lexWord = do
    word <- bumpWhile isIdentifierLike
    let kind = case word of
            "def" -> kDef
            _ -> kIdent
    pure $ Token kind word

isIdentifierLike :: Char -> Bool
isIdentifierLike '_' = True
isIdentifierLike '\'' = True
isIdentifierLike c | isAlphaNum c = True
isIdentifierLike _ = False

runLexerT :: (Monad m) => Text -> LexerT m a -> m (a, [Diagnostic])
runLexerT lxRest lexer = do
    let st =
            LexerState
                { lxRest = lxRest
                , lxCursor = 0
                , lxBuffer = Seq.Empty
                }
    ((result, _), diag) <- runWriterT (runStateT lexer st)
    pure (result, diag)

runLexer :: Text -> LexerT Identity a -> (a, [Diagnostic])
runLexer text = runIdentity . runLexerT text

lexAll :: T.Text -> ([Token], [Diagnostic])
lexAll input = runLexer input go
  where
    go :: LexerT Identity [Token]
    go = do
        token@(Token{tKind}) <- next
        if tKind == kEof
            then pure [token]
            else (token :) <$> go
