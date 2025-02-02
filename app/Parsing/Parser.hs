{-# LANGUAGE LambdaCase #-}
module Parsing.Parser where

import Lexing.Lexer (Token(..), TokenKind(..))
import Parsing.Errors (ParsingError(..))
import Parsing.Tree (ExpressionKind(..), Expression(..))
import Parsing.Type (Type (..))

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
  (t : ts) -> Right (t, t:ts)

expect :: TokenKind -> Parser Token
expect kind = Parser $ \case
  [] -> Left EndOfInput
  (t : ts) -> if tokenKind t == kind
    then Right (t, t:ts)
    else Left $ ExpectedDifferentToken kind t

expr :: Token -> ExpressionKind -> Expression
expr token kind = Expression token kind []

optional :: Parser Token -> Parser (Maybe Token)
optional parser = Parser $ \tokens -> case runParser parser tokens of
  Right (token, rest) -> Right (Just token, rest)
  Left _ -> Right (Nothing, tokens)

parse :: [Token] -> Either ParsingError Expression
parse tokens = do
    (root, _) <- runParser parser tokens
    return root
  where
    parser = do
      bofToken <- consume TokenBOF
      declarations <- parseSequence TokenNewline TokenBOF parseDeclaration
      return $ Expression bofToken RootExpr declarations

parseDeclaration :: Parser Expression
parseDeclaration = do
  token <- peek
  case tokenKind token of
    TokenFn -> parseFunction
    _ -> Parser $ \_ -> Left $ UnexpectedToken token

parseFunction :: Parser Expression
parseFunction = do
  fnToken <- consume TokenFn
  nameToken <- consume TokenIdentifier
  _args 
    <- consumeRelevant TokenLeftParenthesis 
    >> parseFluidSequence TokenRightParenthesis (consume TokenIdentifier)
    <* consumeRelevant TokenRightParenthesis

  _returnTypeToken <- consume TokenReturns
  fnReturnType <- parseType
  let name = tokenValue nameToken

  return $ expr fnToken (FunctionExpr name fnReturnType)

parseType :: Parser Type
parseType = do
  nextToken <- peek
  case tokenKind nextToken of
    TokenLeftParenthesis -> do
      _ <- consume TokenLeftParenthesis
      types <- parseFluidSequence TokenRightParenthesis (parseType)
      _ <- consume TokenRightParenthesis  
      return $ TupleType types
    TokenIdentifier -> do
      typeToken <- consume TokenIdentifier
      return $ case tokenValue typeToken of
        "Int" -> IntType
        other -> UnknownType other
    _ -> failParser $ InvalidTokenForType nextToken

failParser :: ParsingError -> Parser a
failParser err = Parser $ \_ -> Left err

parseSequence :: TokenKind -> TokenKind -> Parser a -> Parser [a]
parseSequence separator end itemParser = Parser $ \tokens -> do
    let parseNext acc remaining = case runParser (expect end) remaining of
            Right (_, rest) -> Right (reverse acc, rest)
            Left _ -> do
                (item, rest1) <- runParser itemParser remaining
                case rest1 of
                    [] -> Right (reverse (item:acc), [])
                    _ -> case runParser (consume separator) rest1 of
                        Right (_, rest2) -> parseNext (item:acc) rest2
                        Left err -> Left err
    parseNext [] tokens

parseFluidSequence :: TokenKind -> Parser a -> Parser [a]
parseFluidSequence  end itemParser = Parser $ \tokens -> do
    let parseNext acc remaining = case runParser (expect end) remaining of
            Right (_, rest) -> Right (reverse acc, rest)
            Left _ -> do
                (item, rest1) <- runParser itemParser remaining
                case rest1 of
                    [] -> Right (reverse (item:acc), [])
                    _ -> case parseNext (item:acc) rest1 of
                        Right (_, rest2) -> Right (reverse acc, rest2)
                        Left err -> Left err
    parseNext [] tokens