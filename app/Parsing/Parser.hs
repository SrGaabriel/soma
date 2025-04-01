{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Parsing.Parser where

import Control.Applicative (Alternative (..), (<|>))
import Control.Monad (when)
import Control.Monad.Error.Class (MonadError (catchError, throwError))
import qualified Data.Map as Map
import Lexing.Lexer (Token (..), TokenKind (..))
import Parsing.Errors (ParsingError (..))
import Parsing.Ops (BinaryOp (..))
import Parsing.Tree (Expression (..), ExpressionKind (..))
import Parsing.Type (GenericConstraint (..), Type (..))
import Utils.Constraints (applyClassConstraint)
import Utils.Currying (uncurryFunction)
import Utils.Lists (hardHead)

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

peekRelevantSkipping :: Int -> Parser Token
peekRelevantSkipping minIndent = go False
  where
    go sawNewline = Parser $ \case
        [] -> Left EndOfInput
        (t : ts)
            | tokenKind t == TokenNewline -> runParser (go True) ts
            | not sawNewline -> Right (t, t : ts)
            | otherwise -> case compare (tokenIndent t) minIndent of
                LT -> Left $ ExpectedAnExpression t
                _ -> Right (t, t : ts)

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
        TokenStruct -> parseStruct
        TokenClass -> parseTypeClass
        TokenNewline -> next >> parseDeclaration
        _ -> Parser $ \_ -> Left $ UnexpectedToken token

parseBinding :: Parser Expression
parseBinding = do
    nameToken <- consume TokenIdentifier
    let name = tokenValue nameToken
    genericConstrants <- parseGenericConstraints
    leftParenthesisArgStart <- optional $ consume TokenLeftParenthesis
    argNames <- case leftParenthesisArgStart of
        Just _ -> do
            parseFluidSequence TokenRightParenthesis (consume TokenIdentifier)
                <* consume TokenRightParenthesis
        Nothing -> do
            parseFluidSequence TokenReturns (consume TokenIdentifier)
     <* consume TokenReturns

    freeType <- parseType
    let constraintizedType = foldr applyClassConstraint freeType genericConstrants

    case constraintizedType of
        FunctionType arg ret -> do
            let (argTypes, returnType) = uncurryFunction arg ret
            argMappings <- ensureSameLengthMap argNames argTypes
            body <- parseFunctionBody
            pure $ Expression nameToken (FunctionExpr name argMappings returnType body)
        _ -> do
            body <- parseFunctionBody
            pure $ Expression nameToken (ConstantBindingExpr name freeType body)

parseGenericConstraints :: Parser [GenericConstraint]
parseGenericConstraints = do
    left <- optional $ consume TokenLeftBracket
    case left of
        Just _ -> do
            constraints <- parseFluidSequence TokenRightBracket parseGenericConstraint <* consume TokenRightBracket
            pure constraints
        Nothing -> pure []

parseGenericConstraint :: Parser GenericConstraint
parseGenericConstraint = do
    generic <- consume TokenIdentifier
    _ <- consumeRelevant TokenColon
    constraint <- consume TokenIdentifier
    pure $ GenericConstraint (tokenValue generic) (tokenValue constraint)

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
            _ <- next <* (optional $ consume TokenNewline)
            expression <- parseExpression
            pure expression
        _ -> throwError $ UnexpectedToken incoming

parsePatternMatchCase :: Parser Expression
parsePatternMatchCase = do
    prefix <- consume TokenPipe
    pattern <- parsePattern

    _arrow <- consumeRelevant TokenRightArrow
    body <- parseExpression
    pure $ Expression prefix (PatternHandlerExpr pattern body)

parsePattern :: Parser Expression
parsePattern = do
    incoming <- peek
    case tokenKind incoming of
        TokenIdentifier -> do
            token <- next
            pure $ expr token (VariablePatternExpr $ tokenValue token)
        TokenNumber -> do
            token <- next
            pure $ expr token (NumberPatternExpr $ tokenValue token)
        _ -> throwError $ UnexpectedToken incoming

parseExpression :: Parser Expression
parseExpression = parseNumericExpression

parseNumericExpression :: Parser Expression
parseNumericExpression = parseBinaryOp parseTerm [TokenPlus, TokenMinus]

parseTerm :: Parser Expression
parseTerm = parseBinaryOp parseApplication [TokenAsterisk, TokenSlash]

parseApplication :: Parser Expression
parseApplication = do
    atoms <-
        someAccepting
            parseAtom
            ( \err -> case err of
                NotAnExpression _ -> True
                ExpectedAnExpression _ -> True
                _ -> False
            )
    if atoms == []
        then do
            inc <- peek
            throwError $ ExpectedAnExpression inc
        else pure $ foldl2 (\f arg -> expr (exprToken f) (FunctionCallExpr f arg)) atoms
  where
    foldl2 _ [] = error "foldl2: empty list"
    foldl2 _ [x] = x
    foldl2 f (x : xs) = foldl f x xs

parseAtom :: Parser Expression
parseAtom = do
    token <- peek
    case tokenKind token of
        TokenNumber -> do
            numToken <- next
            pure $ expr numToken NumberExpr
        TokenLeftParenthesis -> do
            lparen <- consume TokenLeftParenthesis
            contents <- parseCommaSeparatedUntil TokenRightParenthesis parseExpression
            case contents of
                (first : []) -> pure first
                _ -> pure $ expr lparen (TupleExpr contents)
        TokenIdentifier -> do
            idToken <- next
            pure $ expr idToken (ValueReferenceExpr (tokenValue idToken))
        TokenString -> do
            stringToken <- next
            pure $ expr stringToken (StringExpr (tokenValue stringToken))
        TokenLet -> parseLetExpression
        TokenDollar -> do
            _dollar <- next
            parseExpression
        TokenDo -> do
            doToken <- next
            let indent = tokenIndent doToken
            block <- parseIndentedBlock indent parseExpression
            pure $ expr doToken (BlockExpr block)
        TokenTrue -> do
            trueToken <- next
            pure $ expr trueToken (BoolExpr True)
        TokenFalse -> do
            falseToken <- next
            pure $ expr falseToken (BoolExpr False)
        _ -> throwError $ NotAnExpression token

parseLetExpression :: Parser Expression
parseLetExpression = do
    letToken <- consume TokenLet
    identifier <- consume TokenIdentifier
    _ <- consume TokenEquals
    value <- parseExpression
    _ <- consumeRelevant TokenIn

    mapM_ validateIndentation =<< optional (consume TokenNewline)

    body <- parseExpression

    pure $ expr letToken (LetExpr (tokenValue identifier) value body)
  where
    validateIndentation newline =
        let actualIndent = length (tokenValue newline)
            expectedIndent = tokenIndent newline
        in when (actualIndent /= expectedIndent)
            $ throwError
            $ ExpectedDifferentIndentation newline expectedIndent actualIndent

parseStruct :: Parser Expression
parseStruct = do
    structToken <- consume TokenStruct
    nameToken <- consume TokenIdentifier

    genericsDeclared <- optional $ consume TokenLeftBracket
    generics <- case genericsDeclared of
        Just _ -> do
            genericTokens <- parseFluidSequence TokenRightBracket (consume TokenIdentifier) <* consume TokenRightBracket
            pure $ Just $ map (\x -> GenericType (tokenValue x) []) genericTokens
        Nothing -> pure Nothing

    constructors <- parseIndexedIndentedBlock (tokenIndent nameToken) parseStructConstructor
    let name = tokenValue nameToken
    pure $ expr structToken $ StructExpr name constructors generics

parseStructConstructor :: Int -> Parser Expression
parseStructConstructor index = do
    firstToken <-
        if index == 0
            then consume TokenEquals
            else consume TokenPipe
    nameToken <- consume TokenIdentifier
    fields <- parseIndentedBlock (tokenIndent nameToken) parseStructField
    pure $ expr firstToken $ StructConstructorExpr (tokenValue nameToken) fields

parseStructField :: Parser Expression
parseStructField = do
    nameToken <- consume TokenIdentifier
    _ <- consumeRelevant TokenReturns
    typeExpr <- parseType
    pure $ expr nameToken (StructFieldExpr (tokenValue nameToken) typeExpr)

parseTypeClass :: Parser Expression
parseTypeClass = do
    classToken <- consume TokenClass
    nameToken <- consume TokenIdentifier
    genericToks <- parseFluidSequence TokenWhere (consume TokenIdentifier)
    _where <- consume TokenWhere
    methods <- parseIndentedBlock (tokenIndent nameToken) parseTypeClassMethod
    let name = tokenValue nameToken
    let generics = map tokenValue genericToks
    pure $ expr classToken $ TypeClassExpr name generics methods

parseTypeClassMethod :: Parser Expression
parseTypeClassMethod = do
    methodToken <- consume TokenIdentifier
    _ <- consumeRelevant TokenReturns
    methodType <- parseType
    pure $ expr methodToken $ TypeClassMethodExpr (tokenValue methodToken) methodType

parseType :: Parser Type
parseType = do
    nextToken <- peek
    initialType <- case tokenKind nextToken of
        TokenLeftParenthesis -> do
            _ <- consume TokenLeftParenthesis
            types <- parseSequence TokenComma TokenRightParenthesis (parseType)
            _ <- consume TokenRightParenthesis
            case types of
                [singleType] -> pure singleType
                _ -> pure $ TupleType types
        TokenIdentifier -> do
            typeToken <- consume TokenIdentifier
            let name = tokenValue typeToken
            case name of
                "Int" -> pure IntType
                "String" -> pure StringType
                "Bool" -> pure BoolType
                other ->
                    if hardHead other `elem` ['A' .. 'Z']
                        then do
                            genericTypes <-
                                optional
                                    ( consume TokenLeftBracket
                                        *> parseFluidSequence TokenRightBracket parseType
                                        <* consume TokenRightBracket
                                    )
                            generics <- case genericTypes of
                                Just tokens
                                    | length tokens == 0 -> throwError $ InvalidGenericsList typeToken
                                    | otherwise -> pure $ Just $ tokens
                                Nothing -> pure Nothing
                            pure $ UnresolvedStructType other generics
                        else pure $ GenericType other []
        _ -> throwError $ InvalidTokenForType nextToken
    incoming <- peek
    if tokenKind incoming == TokenRightArrow
        then do
            _ <- consumeRelevant TokenRightArrow
            returnType <- parseType
            pure $ FunctionType initialType returnType
        else pure initialType

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

parseSequence :: (Show a) => TokenKind -> TokenKind -> Parser a -> Parser [a]
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
    parseRest = (consume TokenComma *> parseList) <|> (consume end *> pure [])
    checkEmpty = consume end *> pure []

parseExhaustiveSequence :: (Show a) => TokenKind -> Parser a -> Parser [a]
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

parseFluidSequence :: (Show a) => TokenKind -> Parser a -> Parser [a]
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
    | length names == length types = pure . Map.fromList $ zip (map tokenValue names ++ replicate (length types - length names) "_") types
    | otherwise = throwError $ FunctionArgumentLengthMismatch (last names)

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