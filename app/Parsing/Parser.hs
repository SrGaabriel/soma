{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Parsing.Parser where

import Lexing.Lexer (Token(..), TokenKind(..))
import Parsing.Errors (ParsingError(..))
import Parsing.Tree (ExpressionKind(..), Expression(..))
import Parsing.Ops (BinaryOp(..))
import Parsing.Type (Type (..))
import Control.Applicative ((<|>), Alternative(..))
import qualified Data.Map as Map
import Control.Monad.Error.Class (MonadError(throwError, catchError))

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

peekRelevantSkipping :: Int -> Parser Token
peekRelevantSkipping minIndent = go False
  where
    go sawNewline = Parser $ \case
      [] -> Left EndOfInput
      (t : ts)
        | tokenKind t == TokenNewline -> runParser (go True) ts
        | not sawNewline -> Right (t, t:ts)
        | otherwise -> case compare (tokenIndent t) minIndent of
            LT -> Left $ ExpectedIndentation t
            _ -> Right (t, t:ts)

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

optional :: Parser a -> Parser (Maybe a)
optional parser = (Just <$> parser) <|> pure Nothing

parse :: [Token] -> Either ParsingError Expression
parse tokens = do
    (root, _) <- runParser parser tokens
    pure root
  where
    parser = do
      declarations <- parseExhaustiveSequence TokenNewline parseDeclaration
      let bof = Token TokenNewline "" 0 0 -- todo: improve this
      pure $ expr bof (RootExpr declarations)

parseDeclaration :: Parser Expression
parseDeclaration = do
  token <- peek
  case tokenKind token of
    TokenIdentifier -> parseBinding
    TokenNewline -> next >> parseDeclaration
    _ -> Parser $ \_ -> Left $ UnexpectedToken token

parseBinding :: Parser Expression
parseBinding = do
    nameToken <- consume TokenIdentifier
    let name = tokenValue nameToken
    argNames <- parseFluidSequence TokenReturns (consume TokenIdentifier) <* consume TokenReturns

    mParens <- optional (consume TokenLeftParenthesis) -- TODO: consider whether this is a tuple or a function
    case mParens of
        Just _  -> do
            argTypes <- parseFluidSequence TokenRightParenthesis parseType <* consume TokenRightParenthesis <* consume TokenRightArrow
            argMappings <- ensureSameLengthMap argNames argTypes
            returnType <- parseType
            body <- parseFunctionBody
            pure $ Expression nameToken (FunctionExpr name argMappings returnType body)
        Nothing -> do
            constantType <- parseType
            body <- parseFunctionBody
            pure $ Expression nameToken (ConstantBindingExpr name constantType body)

parseFunctionParameter :: Parser Expression
parseFunctionParameter = do
  current <- next
  case tokenKind current of
    TokenIdentifier -> do
      pure $ expr current (VariablePatternExpr $ tokenValue current)
    _ -> throwError $ UnexpectedToken current

parseFunctionBody :: Parser Expression
parseFunctionBody = do
  incoming <- peek
  case tokenKind incoming of
    TokenNewline -> do
        cases <- parseIndentedBlock 0 parsePatternMatchCase
        pure $ Expression incoming (PatternMatchExpr cases)
    TokenEquals -> do
        _ <- next
        expression <- parseExpression
        pure expression
    _ -> throwError $ UnexpectedToken incoming

parsePatternMatchCase :: Parser Expression
parsePatternMatchCase = do
  prefix <- consume TokenPipe
  pattern <- parsePattern

  _arrow <- consumeRelevant TokenRightArrow
  _body <- parseExpression
  pure $ Expression prefix (PatternHandlerExpr pattern)

parsePattern :: Parser Expression
parsePattern = do
  incoming <- peek
  case tokenKind incoming of
    TokenIdentifier -> do
      token <- next
      pure $ expr token (ValueReferenceExpr $ tokenValue token)
    TokenNumber -> do
      token <- next
      pure $ expr token (NumberPatternExpr $ tokenValue token)
    _ -> throwError $ UnexpectedToken incoming

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
    token <- peekRelevantSkipping 1
    case tokenKind token of
        TokenNumber -> do
            _ <- next
            pure $ expr token NumberExpr
        TokenLeftParenthesis -> do
            _ <- next
            numericExpr <- parseNumericExpression
            _ <- consume TokenRightParenthesis
            pure numericExpr
        TokenIdentifier -> parseIdentifierExpression
        TokenDo -> do
            doToken <- next
            let indent = tokenIndent doToken
            block <- parseIndentedBlock indent parseExpression
            pure $ expr doToken (BlockExpr block)
        TokenString -> do
            stringToken <- next
            pure $ expr stringToken (StringExpr $ tokenValue stringToken)
        _ -> throwError $ UnexpectedToken token

parseIdentifierExpression :: Parser Expression
parseIdentifierExpression = do
    incoming <- optional peekNext
    case incoming of
        Just Token { tokenKind = TokenLeftParenthesis } -> parseFunctionCall
        _ -> do
            token <- next
            pure $ expr token (ValueReferenceExpr $ tokenValue token)

parseFunctionCall :: Parser Expression
parseFunctionCall = do
    identifier <- consume TokenIdentifier
    _ <- consume TokenLeftParenthesis
    args <- parseFluidSequence TokenRightParenthesis parseExpression
    _ <- consume TokenRightParenthesis
    let fnName = tokenValue identifier
    pure $ expr identifier (FunctionCallExpr fnName args)

parseType :: Parser Type
parseType = do
  nextToken <- peek
  case tokenKind nextToken of
    TokenLeftParenthesis -> do
      _ <- consume TokenLeftParenthesis
      types <- parseFluidSequence TokenRightParenthesis (parseType)
      _ <- consume TokenRightParenthesis  
      pure $ TupleType types
    TokenIdentifier -> do
      typeToken <- consume TokenIdentifier
      pure $ case tokenValue typeToken of
        "Int" -> IntType
        "String" -> StringType
        "Bool" -> BoolType
        other -> UnresolvedStructType other
    _ -> throwError $ InvalidTokenForType nextToken

ignoreLine :: Parser ()
ignoreLine = Parser $ \tokens -> do
  let (_ignored, rest) = span (\t -> tokenKind t /= TokenNewline) tokens
  Right ((), rest)

-- findPositionOfNext :: Int -> TokenKind -> Parser Int
-- findPositionOfNext offset kind = Parser $ \tokens -> do
--     let findPositionOfNext' :: Int -> [Token] -> Either ParsingError Int
--         findPositionOfNext' _ [] = case tokens of
--             [] -> Left EndOfInput
--             ts ->
--                 let lastToken = last ts in
--                 Right $ tokenPos lastToken + length (tokenValue lastToken)
--         findPositionOfNext' skipped (t:ts) 
--             | tokenKind t == kind && skipped < offset = 
--                 findPositionOfNext' (skipped + 1) ts
--             | tokenKind t == kind = 
--                 Right (tokenPos t)
--             | otherwise = 
--                 findPositionOfNext' skipped ts
--     rest <- findPositionOfNext' 0 tokens
--     pure (rest, tokens)

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

parseFluidSequence :: Show a => TokenKind -> Parser a -> Parser [a]
parseFluidSequence  end itemParser = Parser $ \tokens -> do
    let parseNext acc remaining = case runParser (expect end) remaining of
            Right (_, rest) -> Right (reverse acc, rest)
            Left _ -> do
                (item, rest') <- runParser itemParser remaining
                case rest' of
                    [] -> Right (reverse (item:acc), [])
                    _ -> case parseNext (item:acc) rest' of
                        Right (parsed, rest2) -> Right (parsed, rest2)
                        Left err -> Left err
    let value = parseNext [] tokens
    case value of
        Right (a, b) -> Right (a, b)
        Left err -> Left err

parseIndentedBlock :: Int -> Parser a -> Parser [a]
parseIndentedBlock previousIndent itemParser = Parser $ \tokens -> do
    indentation <- case tokens of
        [] -> Left EndOfInput
        (t@Token { tokenKind = TokenNewline }:_) ->
            if length (tokenValue t) > previousIndent
                then Right $ length $ tokenValue t
                else Left $ ExpectedIndentation t
        (t:_) -> Left $ ExpectedDifferentToken TokenNewline t

    let parseNext acc remaining = case remaining of
           [] -> Right (reverse acc, [])
           (tok:rest) ->
                let isNewline = tokenKind tok == TokenNewline
                in if isNewline then
                    case rest of
                        (nextTok:_) | tokenKind nextTok == TokenNewline ->
                            parseNext acc rest
                        [] ->
                            parseNext acc rest
                        _ ->
                            let tokenIndentation = length (tokenValue tok)
                            in case compare tokenIndentation indentation of
                                EQ -> do
                                    (item, rest') <- runParser itemParser rest
                                    parseNext (item:acc) rest'
                                LT -> if tokenIndentation == previousIndent 
                                        then Right (reverse acc, remaining)
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
          _ -> pure left

toBinaryOp :: TokenKind -> Maybe BinaryOp
toBinaryOp = \case
  TokenPlus -> Just BinaryAdd
  TokenMinus -> Just BinarySubtract
  TokenAsterisk -> Just BinaryMultiply
  TokenSlash -> Just BinaryDivide
  _ -> Nothing

ensureSameLengthMap :: [Token] -> [Type] -> Parser (Map.Map String Type)
ensureSameLengthMap names types
    | length names < length types = pure . Map.fromList $ zip (map tokenValue names ++ replicate (length types - length names) "_") types
    | length names > length types = throwError $ FunctionArgumentLengthMismatch (last names)
    | otherwise                   = pure $ Map.fromList (zip (map tokenValue names) types)