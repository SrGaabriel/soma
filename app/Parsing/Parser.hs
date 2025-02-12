{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
module Parsing.Parser where

import Lexing.Lexer (Token(..), TokenKind(..))
import Parsing.Errors (ParsingError(..))
import Parsing.Tree (ExpressionKind(..), Expression(..))
import Parsing.Ops (BinaryOp(..))
import Parsing.Type (Type (..))

newtype Parser a = Parser {
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
  (t : ts) -> Right (t, t:ts)

skipping :: Int -> Parser Token
skipping n = Parser $ \case
  [] -> Left EndOfInput
  (t : ts) -> Right (t, drop n ts)

expect :: TokenKind -> Parser Token
expect kind = Parser $ \case
  [] -> Left EndOfInput
  (t : ts) -> if tokenKind t == kind
    then Right (t, t:ts)
    else Left $ ExpectedDifferentToken kind t

expr :: Token -> ExpressionKind -> Expression
expr token kind = Expression token kind

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
      declarations <- parseSequence TokenNewline TokenEOF parseDeclaration
      return $ Expression bofToken (RootExpr declarations)

parseDeclaration :: Parser Expression
parseDeclaration = do
  token <- peek
  case tokenKind token of
    TokenFn -> parseFunction
    TokenNewline -> next >> parseDeclaration
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

  body <- parseFunctionBody

  let name = tokenValue nameToken

  return $ Expression fnToken (FunctionExpr name fnReturnType body)

parseFunctionBody :: Parser Expression
parseFunctionBody = do
  incoming <- peek
  case tokenKind incoming of
    TokenNewline -> do
      cases <- parseIndentedBlock 2 parsePatternMatchCase
      return $ Expression incoming (PatternMatchExpr cases)
    TokenEquals -> do
      _equals <- next
      expression <- parseExpression
      return expression
    _ -> failParser $ UnexpectedToken incoming

parsePatternMatchCase :: Parser Expression
parsePatternMatchCase = do
  prefix <- consume TokenPipe
  pattern <- parsePattern

  _arrow <- consumeRelevant TokenRightArrow
  _body <- ignoreLine
  return $ Expression prefix (PatternHandlerExpr pattern)

parsePattern :: Parser Expression
parsePattern = do
  incoming <- peek
  case tokenKind incoming of
    TokenIdentifier -> do
      token <- next
      return $ expr token (VariablePatternExpr $ tokenValue token)
    TokenNumber -> do
      token <- next
      return $ expr token (NumberPatternExpr $ tokenValue token)
    _ -> failParser $ UnexpectedToken incoming

parseExpression :: Parser Expression
parseExpression = do
  parseNumericExpression -- TODO: implement equals

parseNumericExpression :: Parser Expression
parseNumericExpression = parseBinaryOp 
  parseTerm 
  [TokenPlus, TokenMinus]

parseTerm :: Parser Expression
parseTerm = parseBinaryOp 
  parseFactor 
  [TokenAsterisk, TokenSlash]

parseFactor :: Parser Expression
parseFactor = do
  token <- peek
  case tokenKind token of
    TokenNumber -> do
      _ <- next
      return $ expr token NumberExpr
    TokenLeftParenthesis -> do
      _ <- next
      numericExpr <- parseNumericExpression
      _ <- consume TokenRightParenthesis
      return numericExpr
    _ -> failParser $ UnexpectedToken token

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

ignoreLine :: Parser ()
ignoreLine = Parser $ \tokens -> do
  let (_ignored, rest) = span (\t -> tokenKind t /= TokenNewline) tokens
  Right ((), rest)

parseSequence :: Show a => TokenKind -> TokenKind -> Parser a -> Parser [a]
parseSequence separator end itemParser = Parser $ \tokens -> do
    parseNext [] tokens
    where
        parseNext acc remaining = do
            (item, rest) <- runParser itemParser remaining
            case rest of 
                [] -> Right (reverse (item:acc), [])
                _ -> do
                  (tokenPeek, _) <- runParser next rest
                  case tokenKind tokenPeek of
                      tk | tk == separator -> do
                          _ <- runParser next rest
                          parseNext (item:acc) rest
                        | tk == end -> Right (reverse (item:acc), rest)
                        | otherwise -> Left $ ExpectedDifferentToken separator tokenPeek

parseFluidSequence :: TokenKind -> Parser a -> Parser [a]
parseFluidSequence  end itemParser = Parser $ \tokens -> do
    let parseNext acc remaining = case runParser (expect end) remaining of
            Right (_, rest) -> Right (reverse acc, rest)
            Left _ -> do
                (item, rest') <- runParser itemParser remaining
                case rest' of
                    [] -> Right (reverse (item:acc), [])
                    _ -> case parseNext (item:acc) rest' of
                        Right (_, rest2) -> Right (reverse acc, rest2)
                        Left err -> Left err
    parseNext [] tokens

parseIndentedBlock :: Int -> Parser a -> Parser [a]
parseIndentedBlock minimumIndent itemParser = Parser $ \tokens -> do
   let parseNext acc remaining = case remaining of
           [] -> Right (reverse acc, [])
           (tok:rest)
               | tokenKind tok == TokenNewline && length (tokenValue tok) >= minimumIndent -> do
                  (item, rest') <- runParser itemParser rest
                  parseNext (item:acc) rest'
               | otherwise -> Right (reverse acc, remaining)
   parseNext [] tokens

parseBinaryOp :: Parser Expression -> [TokenKind] -> Parser Expression
parseBinaryOp term operatorTokens = do
  left <- term
  loop left
  where
    loop left = do
      mt <- optional peek
      case mt of
          Just t 
            | tokenKind t `elem` operatorTokens
            , Just op <- toBinaryOp (tokenKind t) -> do
              _ <- next
              right <- term
              loop $ expr t (BinaryOpExpr left right op)
          _ -> return left

toBinaryOp :: TokenKind -> Maybe BinaryOp
toBinaryOp = \case
  TokenPlus -> Just BinaryAdd
  TokenMinus -> Just BinarySubtract
  TokenAsterisk -> Just BinaryMultiply
  TokenSlash -> Just BinaryDivide
  _ -> Nothing