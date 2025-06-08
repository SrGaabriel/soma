module Parsing.Types where

import Parsing.Parser (Parser, optional, consume)
import Typing.Types (Kind(..), Type (..), TyConstructor (TypeConstructor), TyVar (TypeVar))
import Lexing.Lexer (TokenKind(..), Token (tokenValue))
import Control.Applicative ((<|>), Alternative (many))

parseKind :: Parser Kind
parseKind = parseKindArrow
  where
    parseKindArrow = do
      k1 <- parseKindAtom
      rest <- optional (consume TokenLeftArrow *> parseKindArrow)
      case rest of
        Just k2 -> pure $ KindArrow k1 k2
        Nothing -> pure k1
    
    parseKindAtom = 
      (consume TokenAsterisk *> pure KindStar) <|>
      (consume TokenLeftParen *> parseKind <* consume TokenRightParen)

parseType :: Parser Type
parseType = do
  baseType <- parseSimpleType
  maybeConstraints <- optional (consume TokenWhere *> parseWhereConstraints)
  case maybeConstraints of
    Just constraints -> 
      pure $ addConstraintsToType baseType constraints
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
  (TVar <$> parseTyVar) <|>
  (TConstructor <$> parseTyConstructor) <|>
  parseParenthesizedType
  where
    parseParenthesizedType = do
      _ <- consume TokenLeftParen
      firstType <- parseType
      rest <- many (consume TokenComma *> parseType)
      _ <- consume TokenRightParen
      case rest of
        [] -> pure firstType  -- Single parenthesized type
        _ -> pure $ foldl TApp (TConstructor $ TypeConstructor "Tuple" KindStar) (firstType : rest)

parseWhereConstraints :: Parser [(String, Type)]
parseWhereConstraints = do
  firstConstraint <- parseTypeVarConstraint
  rest <- many (parseConstraintSeparator *> parseTypeVarConstraint)
  pure (firstConstraint : rest)
  where
    parseConstraintSeparator = 
      (consume TokenComma) <|> 
      (consume TokenNewline)
    
    parseTypeVarConstraint = do
      tyVarName <- consume TokenIdentifier
      _ <- consume TokenColon
      constraintType <- parseConstraintType
      pure (tokenValue tyVarName, constraintType)

parseConstraintType :: Parser Type
parseConstraintType = 
  parseSimpleConstraint <|>
  parseConstraintTuple
  where
    parseSimpleConstraint = do
      className <- consume TokenIdentifier
      args <- many parseAtomType
      let baseCon = TConstructor $ TypeConstructor (tokenValue className) KindStar
      pure $ foldl TApp baseCon args
    
    parseConstraintTuple = do
      _ <- consume TokenLeftParen
      firstConstraint <- parseConstraintType
      restConstraints <- many (consume TokenComma *> parseConstraintType)
      _ <- consume TokenRightParen
      case restConstraints of
        [] -> pure firstConstraint
        _ -> pure $ foldl TApp (TConstructor $ TypeConstructor "ConstraintTuple" KindStar) 
                              (firstConstraint : restConstraints)

parseTyVar :: Parser TyVar
parseTyVar = do
  name <- consume TokenIdentifier
  kind <- optional (consume TokenReturns *> parseKind)
  pure $ TypeVar (tokenValue name) (maybe KindStar id kind)

parseTyConstructor :: Parser TyConstructor
parseTyConstructor = do
  name <- consume TokenIdentifier
  kind <- optional (consume TokenReturns *> parseKind)
  pure $ TypeConstructor (tokenValue name) (maybe KindStar id kind)

addConstraintsToType :: Type -> [(String, Type)] -> Type
addConstraintsToType baseType constraints = 
  let constraintType = foldl TApp 
                           (TConstructor $ TypeConstructor "WhereConstraints" KindStar)
                           (map constraintToType constraints)
      constraintToType (varName, constraintExpr) = 
        TApp (TApp (TConstructor $ TypeConstructor "TypeConstraint" KindStar)
                   (TConstructor $ TypeConstructor varName KindStar))
             constraintExpr
  in TApp (TApp (TConstructor $ TypeConstructor "ConstrainedType" KindStar)
                baseType)
          constraintType