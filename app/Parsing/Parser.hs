{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
module Parsing.Parser where

import Lexing.Lexer (Token(..), TokenKind(..))
import Parsing.Errors (ParsingError(..))
import Parsing.Tree (ExpressionKind(..), Expression(..))
import Parsing.Ops (BinaryOp(..))
import Parsing.Type (Type (..))
import qualified Debug.Trace as Debug

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

peekNext :: Parser Token
peekNext = Parser $ \case
  [] -> Left EndOfInput
  (f : t : ts) -> Right (t, f:t:ts)
  [_] -> Left EndOfInput

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
      declarations <- parseExhaustiveSequence TokenNewline parseDeclaration
      let bof = Token TokenNewline "" 0 0 -- todo: improve this
      return $ expr bof (RootExpr declarations)

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
        cases <- parseIndentedBlock 0 parsePatternMatchCase
        return $ Expression incoming (PatternMatchExpr cases)
    TokenEquals -> do
        _ <- next
        expression <- parseExpression
        return expression
    _ -> failParser $ UnexpectedToken incoming

parsePatternMatchCase :: Parser Expression
parsePatternMatchCase = do
  prefix <- consume TokenPipe
  pattern <- parsePattern

  _arrow <- consumeRelevant TokenRightArrow
  _body <- parseExpression
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
    parseNumericExpression

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
        TokenIdentifier -> parseIdentifierExpression
        TokenDo -> do
            doToken <- next
            let indent = tokenIndent doToken
            block <- parseIndentedBlock indent parseExpression
            return $ expr doToken (BlockExpr block)
        _ -> failParser $ UnexpectedToken token

parseIdentifierExpression :: Parser Expression
parseIdentifierExpression = do
    incoming <- peekNext
    Debug.traceM $ "Identifier expression: " ++ show incoming
    case tokenKind incoming of
        TokenLeftParenthesis -> parseFunctionCall
        _ -> do
            token <- next
            return $ expr token (VariableReferenceExpr $ tokenValue token)

parseFunctionCall :: Parser Expression
parseFunctionCall = do
    identifier <- consume TokenIdentifier
    _ <- consume TokenLeftParenthesis
    args <- parseFluidSequence TokenRightParenthesis parseExpression
    _ <- consume TokenRightParenthesis
    let fnName = tokenValue identifier
    return $ expr identifier (FunctionCallExpr fnName args)

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
                [] -> Left EndOfInput
                _ -> do
                  (tokenPeek, _) <- runParser next rest
                  case tokenKind tokenPeek of
                      tk | tk == separator -> do
                          _ <- runParser next rest
                          parseNext (item:acc) rest
                        | tk == end -> Right (reverse (item:acc), rest)
                        | otherwise -> Left $ ExpectedDifferentToken separator tokenPeek

parseExhaustiveSequence :: Show a => TokenKind -> Parser a -> Parser [a]
parseExhaustiveSequence separator itemParser = Parser $ \tokens -> do
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
parseIndentedBlock previousIndent itemParser = Parser $ \tokens -> do
    indentation <- case tokens of
        [] -> Left EndOfInput
        (t@Token { tokenKind = TokenNewline }:_) -> if length (tokenValue t) > previousIndent
            then Right $ length (tokenValue t)
            else Left $ ExpectedIndentation t

        (t:_) -> Left $ ExpectedDifferentToken TokenNewline t

    let parseNext acc remaining = case remaining of
           [] -> Right (reverse acc, [])
           (tok:rest) ->
                let kind = tokenKind tok
                    isNewline = kind == TokenNewline
                    tokenIndentation = length (tokenValue tok)
                in if isNewline then case compare tokenIndentation indentation of
                    EQ -> do
                        (item, rest') <- runParser itemParser rest
                        parseNext (item:acc) rest'
                    LT -> if tokenIndentation == previousIndent then Right (reverse acc, remaining)
                          else Left $ ExpectedDifferentIndentation tok indentation tokenIndentation
                    GT -> Left $ ExpectedDifferentIndentation tok indentation tokenIndentation
                else Left $ UnseparatedStatements tok

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