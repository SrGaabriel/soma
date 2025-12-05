module Parsing.DataTypes (parseDataType, parseDataTypeWithAttributes) where

import Lexing.Lexer (Token (tokenValue), TokenKind (..), spanningTokens)
import Lexing.Position (Located)
import Parsing.Parser (Parser, consume, parseFluidSequence, parseLayout, parseOptionallyLayout)
import Parsing.Types (parseLocatedType, parseTyVar)
import Syntax.Tree (Attribute, Expr (..))
import Typing.Types (Type)

parseDataType :: Parser Expr
parseDataType = parseDataTypeWithAttributes []

parseDataTypeWithAttributes :: [Located Attribute] -> Parser Expr
parseDataTypeWithAttributes attrs = do
    dataTok <- consume TokenData
    nameTok <- consume TokenUpperIdentifier
    tyVars <- parseFluidSequence TokenLayoutStart parseTyVar

    let name = tokenValue nameTok
        spanning = spanningTokens dataTok nameTok
    constructors <- parseLayout parseDataTypeConstructor
    pure
        $ ExprDataTypeDef
            { dataName = name
            , dataGenerics = tyVars
            , dataConstraints = []
            , dataConstructors = constructors
            , dataAttributes = attrs
            , dataSpan = spanning
            }

parseDataTypeConstructor :: Parser Expr
parseDataTypeConstructor = do
    firstToken <- consume TokenPipe
    nameToken <- consume TokenUpperIdentifier
    fields <- parseOptionallyLayout parseDataTypeConstructorField
    pure
        $ ExprDataConstructor
            { structConstructorName = tokenValue nameToken
            , structConstructorArgs = fields
            , structConstructorSpan = spanningTokens firstToken nameToken
            }

parseDataTypeConstructorField :: Parser (String, Located Type)
parseDataTypeConstructorField = do
    nameToken <- consume TokenLowerIdentifier
    _ <- consume TokenReturns
    typeExpr <- parseLocatedType
    pure (tokenValue nameToken, typeExpr)
