{-# LANGUAGE LambdaCase #-}
module Parsing.Parser where

import Lexing.Lexer (Token(..), TokenKind(..))
import Parsing.Errors (ParsingError(..))
import Parsing.Tree (ExpressionKind(..), Expression(..))

data Parser a = Parser {
  runParser :: [Token] -> Either ParsingError (a, [Token])
}

instance Functor Parser where
  fmap f (Parser p) = Parser $ \tokens -> do
    (x, rest) <- p tokens
    Right (f x, rest)

instance Applicative Parser where
  pure x = Parser $ \tokens -> Right(x, tokens)
  Parser p1 <*> Parser p2 = Parser $ \tokens -> do
    (f, rest1) <- p1 tokens
    (x, rest2) <- p2 rest1
    Right (f x, rest2)

instance Monad Parser where
  Parser p >>= f = Parser $ \tokens -> do
    (x, rest) <- p tokens
    let Parser p2 = f x
    p2 rest

consume :: TokenKind -> Parser Token
consume expectedKind = Parser $ \case
  [] -> Left EndOfInput
  (t : ts)
    | tokenKind t == expectedKind -> Right (t, ts)
    | otherwise -> Left $ ExpectedDifferentToken expectedKind t

peek :: Parser Token
peek = Parser $ \case
  [] -> Left EndOfInput
  (t : ts) -> Right (t, t:ts)

expr :: Token -> ExpressionKind -> Expression
expr token kind = Expression token kind []

parse :: [Token] -> Either ParsingError Expression
parse tokens = do
    (root, _) <- runParser parser tokens
    return root
  where
    parser = do
      bofToken <- consume TokenBOF
      declarations <- parseSequence TokenNewline TokenBOF parseExpression
      return $ Expression bofToken RootExpr declarations

parseExpression :: Parser Expression
parseExpression = do
  token <- peek
  case tokenKind token of
    TokenFn -> do
      fnToken <- consume TokenFn
      _identToken <- consume TokenIdentifier
      return $ expr fnToken FunctionExpr
    _ -> Parser $ \_ -> Left $ UnexpectedToken token

parseSequence :: TokenKind -> TokenKind -> Parser a -> Parser [a]
parseSequence separator end itemParser = Parser $ \tokens -> do
    let parseNext acc remaining = case runParser (consume end) remaining of
            Right (_, rest) -> Right (reverse acc, rest)
            Left _ -> do
                (item, rest1) <- runParser itemParser remaining
                case rest1 of
                    [] -> Right (reverse (item:acc), [])
                    _ -> case runParser (consume separator) rest1 of
                        Right (_, rest2) -> parseNext (item:acc) rest2
                        Left err -> Left err  -- Now we propagate the separator error
    parseNext [] tokens