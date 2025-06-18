{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Parsing.Parser where

import Control.Applicative (Alternative (..))
import Control.Monad.Error.Class (MonadError (..))
import Lexing.Lexer (Token (..), TokenKind (..))
import Parsing.Errors (ParsingError (..))

newtype Parser a = Parser
    { runParser :: [Token] -> Either ParsingError (a, [Token])
    }

instance Functor Parser where
    fmap f (Parser p) = Parser $ \tokens -> do
        (x, rest) <- p tokens
        Right (f x, rest)

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

consumeRelevant :: TokenKind -> Parser Token
consumeRelevant expectedKind = Parser $ \case
    [] -> Left EndOfInput
    (t : ts)
        | tokenKind t == TokenNewline -> runParser (consumeRelevant expectedKind) ts
        | tokenKind t == expectedKind -> Right (t, ts)
        | otherwise -> Left $ ExpectedDifferentToken expectedKind t

peek :: Parser Token
peek = Parser $ \case
    [] -> Left EndOfInput
    (t : ts) -> Right (t, t : ts)

peekRelevant :: Parser Token
peekRelevant = Parser $ \case
    [] -> Left EndOfInput
    (t : ts) -> case seeIfNewline (t : ts) of
        Left err -> Left err
        Right (token, _) -> Right (token, t : ts)
  where
    seeIfNewline = \case
        [] -> Left EndOfInput
        (t : ts)
            | tokenKind t == TokenNewline -> runParser peekRelevant ts
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
        endCheck <- runParser (peek) remaining
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
    checkEmpty = confirm end *> pure []

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
                            _ <- runParser next rest
                            parseNext (item : acc) rest
                        | otherwise -> Left $ ExpectedDifferentToken separator tokenPeek

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

parseIndentedBlock :: Int -> Parser a -> Parser [a]
parseIndentedBlock previousIndent itemParser = Parser $ \tokens -> do
    indentation <- case tokens of
        (t@Token{tokenKind = TokenNewline} : _) ->
            if length (tokenValue t) > previousIndent
                then Right $ length $ tokenValue t
                else Left $ ExpectedIndentation t
        (t : _) -> Left $ ExpectedDifferentToken TokenNewline t
        _ -> Left EndOfInput

    let parseNext acc remaining = case remaining of
            [] -> Right (reverse acc, [])
            (tok : rest) ->
                let isNewline = tokenKind tok == TokenNewline
                in if isNewline
                    then case rest of
                        (nextTok : _)
                            | tokenKind nextTok == TokenNewline ->
                                parseNext acc rest
                        [] ->
                            parseNext acc rest
                        _ ->
                            let tokenIndentation = length (tokenValue tok)
                            in case compare tokenIndentation indentation of
                                EQ -> do
                                    (item, rest') <- runParser itemParser rest
                                    parseNext (item : acc) rest'
                                LT -> Right (reverse acc, remaining)
                                GT -> Left $ ExpectedDifferentIndentation tok indentation tokenIndentation
                    else Right (reverse acc, remaining)
    parseNext [] tokens

-- TODO: remove repeated code
parseIndexedIndentedBlock :: Int -> (Int -> Parser a) -> Parser [a]
parseIndexedIndentedBlock previousIndent itemParser = Parser $ \tokens -> do
    indentation <- case tokens of
        (t@Token{tokenKind = TokenNewline} : _) ->
            if length (tokenValue t) > previousIndent
                then Right $ length $ tokenValue t
                else Left $ ExpectedIndentation t
        (t : _) -> Left $ ExpectedDifferentToken TokenNewline t
        _ -> Left EndOfInput

    let parseNext acc remaining = case remaining of
            [] -> Right (reverse acc, [])
            (tok : rest) ->
                let isNewline = tokenKind tok == TokenNewline
                in if isNewline
                    then case rest of
                        (nextTok : _)
                            | tokenKind nextTok == TokenNewline ->
                                parseNext acc rest
                        [] ->
                            parseNext acc rest
                        _ ->
                            let tokenIndentation = length (tokenValue tok)
                            in case compare tokenIndentation indentation of
                                EQ -> do
                                    let index = length acc
                                    (item, rest') <- runParser (itemParser index) rest
                                    parseNext (item : acc) rest'
                                LT -> Right (reverse acc, remaining)
                                GT -> Left $ ExpectedDifferentIndentation tok indentation tokenIndentation
                    else Right (reverse acc, remaining)
    parseNext [] tokens

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

sepBy1 :: Parser a -> Parser b -> Parser [a]
sepBy1 p sep = (:) <$> p <*> many (sep *> p)

option :: a -> Parser a -> Parser a
option def parser = Parser $ \tokens ->
    case runParser parser tokens of
        Right (result, rest) -> Right (result, rest)
        Left _ -> Right (def, tokens)
