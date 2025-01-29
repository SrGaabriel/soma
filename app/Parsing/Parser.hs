module Parsing.Parser where

import Lexing.Lexer (Token(..))
import Parsing.Errors (ParsingError(..))

data Expression = Expression
  { token :: Token
  , children :: [Expression]
  } deriving (Show, Eq)

data Parser a = Parser {
  parse :: [Token] -> Either ParsingError (a, [Token])
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