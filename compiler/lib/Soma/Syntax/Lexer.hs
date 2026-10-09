{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

module Soma.Syntax.Lexer (
    LexerT,
    LexerState,
    Token (..),
    tRange,
    mkLexerState,
    next,
    peek,
    peekNonTrivial,
    peekNth,
    peekNonTrivialNth,
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
import Maple.Position (Pos, Range (Range))
import Soma.Diagnostic (Diagnostic)
import Soma.Syntax.Kind
import Soma.Util (safeIndex)

data LexerState = LexerState
    { lxRest :: !Text
    , lxCursor :: !Int
    , lxBuffer :: !(Seq Token)
    }

mkLexerState :: Text -> LexerState
mkLexerState txt = LexerState{lxRest = txt, lxCursor = 0, lxBuffer = Seq.empty}

type LexerT m = StateT LexerState (WriterT [Diagnostic] m)

data Token = Token
    { tKind :: !Kind
    , tText :: !Text
    , tOffset :: !Pos
    }
    deriving (Show, Eq)

tRange :: Token -> Range
tRange (Token{tText, tOffset}) =
    let start = tOffset
        end = start + T.length tText
    in Range start end

next :: (Monad m) => LexerT m Token
next = do
    buf <- gets lxBuffer
    case buf of
        t :<| rest -> t <$ modify' (\s -> s{lxBuffer = rest})
        Empty -> lexToken

peek :: (Monad m) => LexerT m Token
peek = peekNth 0

peekNonTrivial :: (Monad m) => LexerT m Token
peekNonTrivial = peekNonTrivialNth 0

peekNth :: (Monad m) => Int -> LexerT m Token
peekNth n = do
    buf <- gets lxBuffer
    case Seq.lookup n buf of
        Just t -> pure t
        Nothing -> do
            t <- lexToken
            modify' (\s -> s{lxBuffer = lxBuffer s |> t})
            peekNth n

peekNonTrivialNth :: (Monad m) => Int -> LexerT m Token
peekNonTrivialNth n = do
    buf <- gets lxBuffer
    let nonTrivialBuf = Seq.filter (not . isTrivia . tKind) buf
    case Seq.lookup n nonTrivialBuf of
        Just t -> pure t
        Nothing -> do
            t <- lexToken
            modify' (\s -> s{lxBuffer = lxBuffer s |> t})
            peekNonTrivialNth n

peekNthChar :: (Monad m) => Int -> LexerT m (Maybe Char)
peekNthChar n = do
    LexerState{lxRest} <- get
    pure $ safeIndex lxRest n

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

emptyToken :: (Monad m) => Kind -> LexerT m Token
emptyToken k = Token k T.empty <$> lxCursor <$> get

charToken :: (Monad m) => Kind -> Char -> LexerT m Token
charToken k c = Token k (T.singleton c) <$> lxCursor <$> get

eofToken :: (Monad m) => LexerT m Token
eofToken = emptyToken KEof

unknownToken :: (Monad m) => Text -> LexerT m Token
unknownToken text = Token KUnknown text <$> lxCursor <$> get

lexToken :: (Monad m) => LexerT m Token
lexToken = do
    mChar <- peekChar
    case mChar of
        Nothing -> eofToken
        Just c -> lexChar c

lexChar :: (Monad m) => Char -> LexerT m Token
lexChar c@'*' = charToken KStar c <* bumpChar
lexChar c@'(' = charToken KLParen c <* bumpChar
lexChar c@')' = charToken KRParen c <* bumpChar
lexChar c@'{' = charToken KLBrace c <* bumpChar
lexChar c@'}' = charToken KRBrace c <* bumpChar
lexChar c@'\n' = charToken KNewline c <* bumpChar
lexChar c@':' = do
    peekNext <- peekNthChar 1
    case peekNext of
        Just '=' -> Token KColonEq ":=" <$> gets lxCursor <* bumpChar <* bumpChar
        _ -> charToken KColon c <* bumpChar
lexChar c
    | isNumber c = lexNumber
    | isAlpha c = lexWord
    | isWhitespace c = lexWhitespace
lexChar c = unknownToken (T.singleton c) <* bumpChar

lexWhitespace :: (Monad m) => LexerT m Token
lexWhitespace = do
    start <- gets lxCursor
    ws <- bumpWhile isWhitespace
    pure (Token KWhitespace ws start)

lexNumber :: (Monad m) => LexerT m Token
lexNumber = do
    start <- gets lxCursor
    num <- bumpWhile isNumber
    pure (Token KNumber num start)

lexWord :: (Monad m) => LexerT m Token
lexWord = do
    start <- gets lxCursor
    word <- bumpWhile isIdentifierLike
    let kind = case word of
            "def" -> KDefKw
            _ -> KIdent
    pure (Token kind word start)

isWhitespace :: Char -> Bool
isWhitespace ' ' = True
isWhitespace _ = False

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
        if tKind == KEof
            then pure [token]
            else (token :) <$> go
