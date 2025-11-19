module Parsing.DataTypes where

import qualified Debug.Trace as Debug
import Lexing.Lexer (Token (tokenValue), TokenKind (..), spanningTokens)
import Parsing.Parser (Parser, consume, parseFluidSequence, parseLayout, parseOptionallyLayout)
import Parsing.Types (parseTyVar, parseType)
import Syntax.Tree (Expr (..))
import Typing.Types (Type)

parseDataType :: Parser Expr
parseDataType = do
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

parseDataTypeConstructorField :: Parser (String, Type)
parseDataTypeConstructorField = do
    Debug.traceM "Parsing data type constructor field"
    nameToken <- consume TokenLowerIdentifier
    Debug.traceM $ "Field name: " ++ tokenValue nameToken
    _ <- consume TokenReturns
    Debug.traceM "Consumed '->' token"
    typeExpr <- parseType
    Debug.traceM $ "Parsed field type: " ++ show typeExpr
    pure (tokenValue nameToken, typeExpr)
