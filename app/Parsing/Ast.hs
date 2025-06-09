{-# LANGUAGE LambdaCase #-}

module Parsing.Ast where

import Control.Applicative (Alternative (many), optional)
import Lexing.Lexer (Token (tokenIndent, tokenKind, tokenValue), TokenKind (..), spanningTokens, tokenSpan)
import Parsing.Atoms (parseExpression)
import Parsing.Bindings (parseBinding)
import Parsing.Errors (ParsingError (UnexpectedToken))
import Parsing.Parser (Parser (Parser, runParser), consume, consumeRelevant, next, parseExhaustiveSequence, parseIndentedBlock, parseIndexedIndentedBlock, peek)
import Parsing.Types (parseTyVarParam, parseType)
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
        TokenLowerIdentifier -> parseBinding
        TokenNewline -> next >> parseDeclaration
        TokenStruct -> parseStruct
        TokenClass -> parseTypeClass
        _ -> Parser $ \_ -> Left $ UnexpectedToken token

parseStruct :: Parser Expr
parseStruct = do
    structToken <- consume TokenStruct
    nameToken <- consume TokenUpperIdentifier

    tyVars <- many parseTyVarParam

    let name = tokenValue nameToken
    let spanning = spanningTokens structToken nameToken
    constructors <- parseIndexedIndentedBlock (tokenIndent nameToken) parseStructConstructor
    pure
        $ ExprStructDef
            { structName = name
            , structGenerics = tyVars
            , structConstructors = constructors
            , structSpan = spanning
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

    tyVars <- many parseTyVarParam

    _where <- consume TokenSpecifies
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
            , typeClassMethodSpan = tokenSpan methodToken
            }
