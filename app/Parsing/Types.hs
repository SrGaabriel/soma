module Parsing.Types where

import Control.Applicative (Alternative (many), (<|>))
import Lexing.Lexer (Token (tokenValue), TokenKind (..))
import Parsing.Parser (Parser, consume, optional, sepBy1)
import Typing.Types (Constraint (Constraint), Kind (..), TyConstructor (TypeConstructor), TyVar (TypeVar), Type (..))

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
        Just constraints ->
            pure $ TConstrained constraints baseType
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
        <|> parseUnresolvedType
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

parseUnresolvedType :: Parser Type
parseUnresolvedType = do
    name <- consume TokenUpperIdentifier
    kind <- optional (consume TokenReturns *> parseKind)
    pure $ TUnresolved (tokenValue name) (maybe KindStar id kind)

parseWhereConstraints :: Parser [Constraint]
parseWhereConstraints = do
    _ <- optional (consume TokenNewline)
    _ <- consume TokenWhere
    concat <$> sepBy1 parseTypeVarConstraint parseConstraintSeparator
  where
    parseConstraintSeparator = consume TokenComma <|> consume TokenNewline

parseTypeVarConstraint :: Parser [Constraint]
parseTypeVarConstraint = do
    tyVarName <- consume TokenLowerIdentifier
    _ <- consume TokenColon
    constraintType <- parseConstraintType

    let varAsType = TVar (TypeVar (tokenValue tyVarName) KindStar)

    let classTypes = flattenConstraintType constraintType
    pure $ map (\classType -> Constraint classType [varAsType]) classTypes

flattenConstraintType :: Type -> [Type]
flattenConstraintType (TTuple types) = types
flattenConstraintType otherType = [otherType]

parseConstraintType :: Parser Type
parseConstraintType =
    parseSimpleConstraint
        <|> parseConstraintTuple
  where
    parseSimpleConstraint = do
        className <- consume TokenUpperIdentifier
        args <- many parseAtomType
        let baseCon = TUnresolved (tokenValue className) KindStar
        pure $ foldl TApp baseCon args

    parseConstraintTuple = do
        _ <- consume TokenLeftParen
        firstConstraint <- parseConstraintType
        restConstraints <- many (consume TokenComma *> parseConstraintType)
        _ <- consume TokenRightParen
        case restConstraints of
            [] -> pure firstConstraint
            _ ->
                pure
                    $ foldl
                        TApp
                        (TConstructor $ TypeConstructor "ConstraintTuple" KindStar)
                        (firstConstraint : restConstraints)

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
