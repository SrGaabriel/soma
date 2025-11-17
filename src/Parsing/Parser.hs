{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Parsing.Parser where

import Control.Applicative (Alternative (..))
import Control.Monad.Error.Class (MonadError (..))
import Data.Functor (($>))
import Lexing.Lexer (Token (..), TokenKind (..))
import Parsing.Errors (ParsingError (..))
import Control.Applicative.Combinators (manyTill)

newtype Parser a = Parser
    { runParser :: [Token] -> Either ParsingError (a, [Token])
    }
    deriving (Functor)

instance Applicative Parser where
    pure x = Parser $ \tokens -> Right (x, tokens)
    Parser p1 <*> Parser p2 = Parser $ \tokens -> do
        (f, rest1) <- p1 tokens
        (x, rest2) <- p2 rest1
        Right (f x, rest2)

instance Monad Parser where
    Parser p >>= f = Parser $ \tokens -> do
        (x, rest) <- p tokens
        let Parser p2 = f x
        p2 rest

instance Alternative Parser where
    empty = Parser $ \_ -> Left EndOfInput
    Parser p1 <|> Parser p2 = Parser $ \tokens -> case p1 tokens of
        Left _ -> p2 tokens
        Right x -> Right x

instance MonadError ParsingError Parser where
    throwError = Parser . const . Left
    catchError (Parser p) handler = Parser $ \tokens -> case p tokens of
        Left err -> runParser (handler err) tokens
        Right x -> Right x

consume :: TokenKind -> Parser Token
consume expectedKind = Parser $ \case
    [] -> Left EndOfInput
    (t : ts)
        | tokenKind t == expectedKind -> Right (t, ts)
        | otherwise -> Left $ ExpectedDifferentToken expectedKind t

confirm :: TokenKind -> Parser ()
confirm expectedKind = Parser $ \case
    [] -> Left EndOfInput
    (t : ts)
        | tokenKind t == expectedKind -> Right ((), t : ts)
        | otherwise -> Left $ ExpectedDifferentToken expectedKind t

next :: Parser Token
next = Parser $ \case
    [] -> Left EndOfInput
    (t : ts) -> Right (t, ts)

peek :: Parser Token
peek = Parser $ \case
    [] -> Left EndOfInput
    (t : ts) -> Right (t, t : ts)

peekInLayout :: Parser Token
peekInLayout = Parser $ \case
    [] -> Left EndOfInput
    (t : ts) -> case seeIfLayout (t : ts) of
        Left err -> Left err
        Right (token, _) -> Right (token, t : ts)
  where
    seeIfLayout = \case
        [] -> Left EndOfInput
        (t : ts)
            | tokenKind t == TokenLayoutStart -> runParser peekInLayout ts
            | otherwise -> Right (t, t : ts)

peekNext :: Parser Token
peekNext = Parser $ \case
    [] -> Left EndOfInput
    (f : t : ts) -> Right (t, f : t : ts)
    [_] -> Left EndOfInput

skipping :: Int -> Parser Token
skipping n = Parser $ \case
    [] -> Left EndOfInput
    (t : ts) -> Right (t, drop n ts)

expect :: TokenKind -> Parser Token
expect kind = Parser $ \case
    [] -> Left EndOfInput
    (t : ts) ->
        if tokenKind t == kind
            then Right (t, t : ts)
            else Left $ ExpectedDifferentToken kind t

optional :: Parser a -> Parser (Maybe a)
optional parser = (Just <$> parser) <|> pure Nothing

parseSequence :: TokenKind -> TokenKind -> Parser a -> Parser [a]
parseSequence separator end itemParser = Parser $ \tokens -> do
    parseNext [] tokens
  where
    parseNext acc remaining = do
        endCheck <- runParser peek remaining
        if tokenKind (fst endCheck) == end
            then Right (reverse acc, remaining)
            else do
                (item, rest) <- runParser itemParser remaining
                case rest of
                    [] -> Left EndOfInput
                    _ -> do
                        (tokenPeek, _) <- runParser peek rest
                        case tokenKind tokenPeek of
                            tk
                                | tk == separator -> do
                                    (_, rest') <- runParser next rest
                                    parseNext (item : acc) rest'
                                | tk == end -> Right (reverse (item : acc), rest)
                                | otherwise -> Left $ ExpectedDifferentToken separator tokenPeek

parseCommaSeparatedUntil :: TokenKind -> Parser a -> Parser [a]
parseCommaSeparatedUntil end itemParser = parseList
  where
    parseList = (:) <$> itemParser <*> parseRest <|> checkEmpty
    parseRest = (consume TokenComma *> parseList) <|> checkEmpty
    checkEmpty = confirm end $> []

parseExhaustiveSequence :: TokenKind -> Parser a -> Parser [a]
parseExhaustiveSequence separator itemParser = Parser $ \tokens -> do
    parseNext [] tokens
  where
    parseNext acc remaining = do
        (item, rest) <- runParser itemParser remaining
        case rest of
            [] -> Right (reverse (item : acc), [])
            _ -> do
                (tokenPeek, _) <- runParser next rest
                case tokenKind tokenPeek of
                    tk
                        | tk == separator -> do
                            (_, afterSeparator) <- runParser next rest
                            parseNext (item : acc) afterSeparator
                        | otherwise -> Right (reverse (item : acc), rest)

parseFluidSequence :: TokenKind -> Parser a -> Parser [a]
parseFluidSequence end itemParser = Parser $ \tokens -> do
    let parseNext acc remaining = case runParser (expect end) remaining of
            Right (_, rest) -> Right (reverse acc, rest)
            Left _ -> do
                (item, rest') <- runParser itemParser remaining
                case rest' of
                    [] -> Right (reverse (item : acc), [])
                    _ -> case parseNext (item : acc) rest' of
                        Right (parsed, rest2) -> Right (parsed, rest2)
                        Left err -> Left err
    let value = parseNext [] tokens
    case value of
        Right (a, b) -> Right (a, b)
        Left err -> Left err

parseInLayout :: Parser a -> Parser a
parseInLayout itemParser =
    consume TokenLayoutStart >> itemParser <* consume TokenLayoutEnd

optionallyParseInLayout :: Parser a -> Parser a
optionallyParseInLayout itemParser = do
    start <- optional (consume TokenLayoutStart)
    case start of
        Just _ -> itemParser <* consume TokenLayoutEnd
        Nothing -> itemParser

parseLayout :: Parser a -> Parser [a]
parseLayout itemParser =
    consume TokenLayoutStart >> sepBy1Until itemParser (consume TokenLayoutSeparator) (consume TokenLayoutEnd)

someAccepting :: Parser a -> (ParsingError -> Bool) -> Parser [a]
someAccepting parser predicate = Parser $ \tokens -> do
    let parseNext acc remaining =
            let result = runParser parser remaining
            in case result of
                Right (item, rest) -> case rest of
                    [] -> Right (reverse (item : acc), [])
                    _ -> parseNext (item : acc) rest
                Left err ->
                    if predicate err
                        then Right (reverse acc, remaining)
                        else Left err
    parseNext [] tokens

optionallySurrounded :: TokenKind -> TokenKind -> Parser a -> Parser a
optionallySurrounded start end parser = do
    startTok <- optional (consume start)
    case startTok of
        Just _ -> do
            result <- parser
            _ <- consume end
            pure result
        Nothing -> parser

sepBy1Until :: Parser a -> Parser sep -> Parser end -> Parser [a]
sepBy1Until p sep end = do
    first <- p
    rest <- manyTill (sep *> p) end
    return (first : rest)

indexedSepBy1Till :: (Int -> Parser a) -> Parser sep -> Parser end -> Parser [a]
indexedSepBy1Till p sep end = go 0
  where
    go n = do
      x <- p n
      xs <- manyTill (sep *> p (n + 1)) end
      return (x : xs)

option :: a -> Parser a -> Parser a
option def parser = Parser $ \tokens ->
    case runParser parser tokens of
        Right (result, rest) -> Right (result, rest)
        Left _ -> Right (def, tokens)

parseFuncName :: Parser String
parseFuncName = do
    inc <- peek
    case tokenKind inc of
        TokenLowerIdentifier ->
            tokenValue <$> next
        TokenLeftBraces -> do
            _ <- next
            nameToken <- consume TokenVarSymbol
            _ <- consume TokenRightBraces
            pure $ tokenValue nameToken
        _ -> throwError $ InvalidFunctionName inc
