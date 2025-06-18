{-# LANGUAGE LambdaCase #-}

module Parsing.Ast where

import Control.Applicative (Alternative (many), optional)
import Control.Monad.Error.Class (MonadError (throwError))
import Lexing.Lexer (Token (tokenIndent, tokenKind, tokenValue), TokenKind (..), spanningTokens)
import Parsing.Atoms (parseExpression)
import Parsing.Bindings (parseBinding)
import Parsing.Errors (ParsingError (UnexpectedToken))
import Parsing.Parser (Parser (runParser), consume, consumeRelevant, next, parseExhaustiveSequence, parseIndentedBlock, parseIndexedIndentedBlock, peek)
import Parsing.Types (parseTyVar, parseType)
import Syntax.Tree (Expr (..))
import Typing.Types (Type)

parse :: [Token] -> Either ParsingError Expr
parse tokens = do
    (root, _) <- runParser parser tokens
    pure root
  where
    parser = do
        declarations <- parseExhaustiveSequence TokenNewline parseDeclaration
        pure $ ExprRoot declarations

parseDeclaration :: Parser Expr
parseDeclaration = do
    token <- peek
    case tokenKind token of
        TokenDef -> parseBinding
        TokenNewline -> next >> parseDeclaration
        TokenData -> parseDataType
        TokenClass -> parseTypeClass
        _ -> throwError $ UnexpectedToken token

parseDataType :: Parser Expr
parseDataType = do
    dataToken <- consume TokenData
    nameToken <- consume TokenUpperIdentifier

    tyVars <- many parseTyVar

    let name = tokenValue nameToken
    let spanning = spanningTokens dataToken nameToken
    constructors <- parseIndexedIndentedBlock (tokenIndent nameToken) parseStructConstructor
    pure
        $ ExprDataTypeDef
            { dataName = name
            , dataGenerics = tyVars
            , dataConstructors = constructors
            , dataSpan = spanning
            }

parseStructConstructor :: Int -> Parser Expr
parseStructConstructor index = do
    firstToken <-
        if index == 0
            then consume TokenEquals
            else consume TokenPipe
    nameToken <- consume TokenUpperIdentifier
    fields <- parseIndentedBlock (tokenIndent nameToken) parseStructField
    pure
        $ ExprStructConstructor
            { structConstructorName = tokenValue nameToken
            , structConstructorArgs = fields
            , structConstructorSpan = spanningTokens firstToken nameToken
            }

parseStructField :: Parser (String, Type)
parseStructField = do
    nameToken <- consume TokenLowerIdentifier
    _ <- consumeRelevant TokenReturns
    typeExpr <- parseType
    pure $ (tokenValue nameToken, typeExpr)

parseTypeClass :: Parser Expr
parseTypeClass = do
    classToken <- consume TokenClass
    nameToken <- consume TokenUpperIdentifier

    tyVars <- many parseTyVar

    _where <- consume TokenWhere
    methods <- parseIndentedBlock (tokenIndent nameToken) parseTypeClassMethod
    let name = tokenValue nameToken
    pure
        $ ExprTypeClassDef
            { typeClassName = name
            , typeClassGenerics = tyVars
            , typeClassMethods = methods
            , typeClassSpan = spanningTokens classToken nameToken
            }

parseTypeClassMethod :: Parser Expr
parseTypeClassMethod = do
    defToken <- consume TokenDef
    methodToken <- consume TokenLowerIdentifier
    _ <- consumeRelevant TokenReturns
    methodType <- parseType

    defaultImpl <-
        (optional $ consume TokenEquals) >>= \case
            Just _ -> Just <$> parseIndentedBlock (tokenIndent methodToken) parseExpression
            Nothing -> pure Nothing

    pure
        $ ExprTypeClassMethod
            { typeClassMethodName = tokenValue methodToken
            , typeClassMethodArgs = []
            , typeClassMethodReturnType = methodType
            , typeClassMethodDefaultImpl = defaultImpl
            , typeClassMethodSpan = spanningTokens defToken methodToken
            }
