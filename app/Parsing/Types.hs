module Parsing.Types where

import Control.Applicative (Alternative (many), (<|>))
import Lexing.Lexer (Token (tokenValue), TokenKind (..))
import Parsing.Parser (Parser, consume, optional, sepBy1)
import Typing.Types (
    Constraint (..),
    Kind (..),
    TyConstructor (..),
    TyVar (..),
    Type (..),
    boolType,
    intType,
    strType,
 )

parseKind :: Parser Kind
parseKind = parseKindArrow
  where
    parseKindArrow = do
        k1 <- parseKindAtom
        rest <- optional (consume TokenRightArrow *> parseKindArrow)
        case rest of
            Just k2 -> pure $ KindArrow k1 k2
            Nothing -> pure k1

    parseKindAtom =
        (consume TokenAsterisk *> pure KindStar)
            <|> (consume TokenLeftParen *> parseKind <* consume TokenRightParen)

parseType :: Parser Type
parseType = do
    baseType <- parseSimpleType
    maybeConstraints <- optional parseWhereConstraints
    case maybeConstraints of
        Just constraints -> pure $ TConstrained constraints baseType
        Nothing -> pure baseType

parseSimpleType :: Parser Type
parseSimpleType = parseForallType <|> parseArrowType

parseForallType :: Parser Type
parseForallType = do
    _ <- consume TokenForall
    tyVar <- parseTyVar
    _ <- consume TokenDot
    bodyType <- parseType
    pure $ TForall tyVar bodyType

parseArrowType :: Parser Type
parseArrowType = do
    t1 <- parseAppType
    rest <- optional (consume TokenRightArrow *> parseArrowType)
    case rest of
        Just t2 -> pure $ TArrow t1 t2
        Nothing -> pure t1

parseAppType :: Parser Type
parseAppType = do
    baseType <- parseAtomType
    args <- many parseAtomType
    pure $ foldl TApp baseType args

parseAtomType :: Parser Type
parseAtomType =
    (TVar <$> parseTyVar)
        <|> parseUnresolvedOrPrimitiveType
        <|> parseParenthesizedType
  where
    parseParenthesizedType = do
        _ <- consume TokenLeftParen
        firstType <- parseType
        rest <- many (consume TokenComma *> parseType)
        _ <- consume TokenRightParen
        case rest of
            [] -> pure firstType
            _ -> pure $ TTuple (firstType : rest)

parseUnresolvedOrPrimitiveType :: Parser Type
parseUnresolvedOrPrimitiveType = do
    name <- consume TokenUpperIdentifier
    kind <- optional (consume TokenReturns *> parseKind)
    let kind' = maybe KindStar id kind
    case tokenValue name of
        "Int" -> pure intType
        "String" -> pure strType
        "Bool" -> pure boolType
        n -> pure $ TUnresolved n kind'

parseWhereConstraints :: Parser [Constraint]
parseWhereConstraints = do
    _ <- optional (consume TokenNewline)
    _ <- consume TokenWhere
    blocks <- sepBy1 parseVarClassConstraint (consume TokenComma <|> consume TokenNewline)
    pure (concat blocks)

parseVarClassConstraint :: Parser [Constraint]
parseVarClassConstraint = do
    varToks <- sepBy1 (consume TokenLowerIdentifier) (consume TokenComma)
    let vars = map (TVar . (`TypeVar` KindStar) . tokenValue) varToks
    _ <- consume TokenColon
    clsToks <- sepBy1 (consume TokenUpperIdentifier) (consume TokenComma)
    let clsNames = map tokenValue clsToks
    pure
        [ Constraint cls [v]
        | cls <- clsNames
        , v <- vars
        ]

parseConstraint :: Parser Constraint
parseConstraint = do
    conTk <- consume TokenUpperIdentifier
    let clsName = tokenValue conTk
    args <- many parseAtomType
    pure $ Constraint clsName args

parseConstraintTuple :: Parser [Constraint]
parseConstraintTuple = do
    _ <- consume TokenLeftParen
    c0 <- parseConstraint
    cs <- many (consume TokenComma *> parseConstraint)
    _ <- consume TokenRightParen
    pure (c0 : cs)

parseTyVar :: Parser TyVar
parseTyVar = parseParenthesizedTyVar <|> parseSimpleTyVar
  where
    parseSimpleTyVar = do
        name <- consume TokenLowerIdentifier
        kind <- optional (consume TokenReturns *> parseKind)
        pure $ TypeVar (tokenValue name) (maybe KindStar id kind)

    parseParenthesizedTyVar = do
        _ <- consume TokenLeftParen
        name <- consume TokenLowerIdentifier
        _ <- consume TokenReturns
        kind <- parseKind
        _ <- consume TokenRightParen
        pure $ TypeVar (tokenValue name) kind

parseTyVarParam :: Parser TyVar
parseTyVarParam = parseTyVar <|> parseParenthesizedTyVarParam

parseParenthesizedTyVarParam :: Parser TyVar
parseParenthesizedTyVarParam = do
    _ <- consume TokenLeftParen
    tyVar <- parseTyVar
    _ <- consume TokenRightParen
    pure tyVar

parseTyConstructor :: Parser TyConstructor
parseTyConstructor = do
    name <- consume TokenUpperIdentifier
    kind <- optional (consume TokenReturns *> parseKind)
    pure $ TypeConstructor (tokenValue name) (maybe KindStar id kind)
