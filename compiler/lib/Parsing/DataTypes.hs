module Parsing.DataTypes (parseDataType, parseDataTypeWithAttributes, parseStructWithAttributes) where

import Lexing.Lexer (Token (tokenKind, tokenValue), TokenKind (..), spanningTokens)
import Lexing.Position (Located)
import Parsing.Parser (Parser, consume, parseExhaustiveSequence, parseFluidSequence, parseLayout, tryPeekOrEOF)
import Parsing.Types (parseLocatedType, parseTyVar)
import Syntax.Tree (Attribute, Expr (..))
import qualified Text.Megaparsec as MP
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

    nextTok <- tryPeekOrEOF
    constructors <- case tokenKind nextTok of
        TokenEquals -> parseInlineConstructors
        _ -> parseLayout parseDataTypeConstructor

    pure
        $ ExprDataTypeDef
            { dataName = name
            , dataGenerics = tyVars
            , dataConstraints = []
            , dataConstructors = constructors
            , dataAttributes = attrs
            , dataSpan = spanning
            }

parseInlineConstructors :: Parser [Expr]
parseInlineConstructors = do
    _ <- consume TokenEquals
    parseExhaustiveSequence TokenPipe parseInlineConstructor

parseInlineConstructor :: Parser Expr
parseInlineConstructor = do
    nameToken <- consume TokenUpperIdentifier
    types <- parseInlineConstructorArgs
    let fields = zipWith (\i t -> ("_" ++ show i, t)) [0 :: Int ..] types
    pure
        $ ExprDataConstructor
            { structConstructorName = tokenValue nameToken
            , structConstructorArgs = fields
            , structConstructorSpan = spanningTokens nameToken nameToken
            }

parseInlineConstructorArgs :: Parser [Located Type]
parseInlineConstructorArgs = go []
  where
    go acc = do
        nextTok <- tryPeekOrEOF
        case tokenKind nextTok of
            TokenPipe -> pure (reverse acc)
            TokenLayoutSeparator -> pure (reverse acc)
            TokenLayoutEnd -> pure (reverse acc)
            TokenLayoutStart -> pure (reverse acc)
            TokenEOF -> pure (reverse acc)
            _ -> do
                mty <- MP.optional parseLocatedType
                case mty of
                    Just ty -> go (ty : acc)
                    Nothing -> pure (reverse acc)

parseStructWithAttributes :: [Located Attribute] -> Parser Expr
parseStructWithAttributes attrs = do
    structTok <- consume TokenStruct
    nameTok <- consume TokenUpperIdentifier
    tyVars <- parseFluidSequence TokenEquals parseTyVar
    _ <- consume TokenEquals
    constructorNameTok <- consume TokenUpperIdentifier

    let name = tokenValue nameTok
        spanning = spanningTokens structTok nameTok

    nextTok <- tryPeekOrEOF
    fields <- case tokenKind nextTok of
        TokenLayoutStart -> parseLayout parseDataTypeConstructorField
        _ -> zipWith (\i t -> ("_" ++ show i, t)) [0 :: Int ..] <$> parseInlineConstructorArgs

    pure
        $ ExprStructDef
            { structName = name
            , structGenerics = tyVars
            , structConstraints = []
            , structConstructorName = tokenValue constructorNameTok
            , structFields = fields
            , structAttributes = attrs
            , structSpan = spanning
            }

parseDataTypeConstructor :: Parser Expr
parseDataTypeConstructor = do
    firstToken <- consume TokenPipe
    nameToken <- consume TokenUpperIdentifier
    nextTok <- tryPeekOrEOF
    fields <- case tokenKind nextTok of
        TokenLayoutStart -> parseLayout parseDataTypeConstructorField
        _ -> zipWith (\i t -> ("_" ++ show i, t)) [0 :: Int ..] <$> parseInlineConstructorArgs
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
