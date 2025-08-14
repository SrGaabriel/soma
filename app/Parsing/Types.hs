module Parsing.Types where

import Control.Monad.Error.Class (MonadError (throwError))
import Data.List (nubBy)
import Lexing.Lexer (Token (tokenKind, tokenValue), TokenKind (..))
import Parsing.Errors (ParsingError (InvalidTokenForType))
import Parsing.Parser (Parser, consume, consumeRelevant, next, parseExhaustiveSequence, parseSequence, peek)
import Typing.Types (Constraint (Constraint), Kind (KindStar, KindArrow), QualifiedType (Forall), TyVar (TypeVar, tvId), Type (TArrow, TUnresolved, TVar, TApp), arrayType, boolType, extractTyVars, intType, strType, tupleType)

parseQualifiedType :: Parser QualifiedType
parseQualifiedType = do
    baseType <- parseType
    incoming <- peek
    if tokenKind incoming == TokenWhere
        then do
            _ <- consumeRelevant TokenWhere
            constraints <- parseExhaustiveSequence TokenComma parseConstraint

            let tyVarsFromType = extractTyVars baseType
            let tyVarsFromConstraints = concatMap (\(Constraint _ tys) -> extractTyVarsFromTypes tys) constraints

            let allVars = deduplicateTyVars (tyVarsFromType ++ tyVarsFromConstraints)

            pure $ Forall allVars constraints baseType
        else do
            let tyVars = extractTyVars baseType
            pure $ Forall tyVars [] baseType

parseType :: Parser Type
parseType = do
    nextToken <- peek
    baseType <- do
        maybeType <- tryParseBaseType
        case maybeType of
            Just t -> pure t
            Nothing -> throwError $ InvalidTokenForType nextToken
    parseTypeRest baseType

parseTypeRest :: Type -> Parser Type
parseTypeRest baseType = do
    incoming <- peek
    case tokenKind incoming of
        TokenRightArrow -> do
            _ <- consumeRelevant TokenRightArrow
            TArrow baseType <$> parseType
        _ -> do
            appType <- tryParseBaseType
            case appType of
                Nothing -> pure baseType
                Just appType' -> do
                    let appliedType = TApp baseType appType'
                    parseTypeRest appliedType

tryParseBaseType :: Parser (Maybe Type)
tryParseBaseType = do
    nextToken <- peek
    case tokenKind nextToken of
        TokenLeftParen -> do
            _ <- next
            types <- parseSequence TokenComma TokenRightParen parseType
            _ <- consume TokenRightParen
            case types of
                [singleType] -> pure $ Just singleType
                _ -> pure $ Just $ tupleType types
        TokenLeftBracket -> do
            _ <- next
            innerType <- parseType
            _ <- consume TokenRightBracket
            pure $ Just $ arrayType innerType
        TokenUpperIdentifier -> Just <$> parseTypeConstructor
        TokenLowerIdentifier -> do
            _ <- next
            let name = tokenValue nextToken
            pure $ Just $ TVar (TypeVar name KindStar)
        _ -> pure Nothing

parseTyVar :: Parser TyVar
parseTyVar = do
    nameTok <- consume TokenLowerIdentifier
    let name = tokenValue nameTok
    pure $ TypeVar name KindStar

parseTypeConstructor :: Parser Type
parseTypeConstructor = do
    name <- consume TokenUpperIdentifier
    case tokenValue name of
        "Int" -> pure intType
        "String" -> pure strType
        "Bool" -> pure boolType
        other -> pure $ TUnresolved other

parseConstraint :: Parser Constraint
parseConstraint = do
    varName <- consume TokenLowerIdentifier
    _ <- consume TokenColon
    className <- consume TokenUpperIdentifier
    let name = tokenValue varName
    pure $ Constraint (tokenValue className) [TVar (TypeVar name KindStar)]

parseKind :: Parser Kind
parseKind = do
    nextToken <- peek
    case tokenKind nextToken of
        TokenVarSymbol | tokenValue nextToken == "*" -> do
            _ <- next
            incoming <- peek
            case tokenKind incoming of
                TokenRightArrow -> do
                    _ <- consumeRelevant TokenRightArrow
                    KindArrow KindStar <$> parseKind
                _ -> pure KindStar
        _ -> throwError $ InvalidTokenForType nextToken

deduplicateTyVars :: [TyVar] -> [TyVar]
deduplicateTyVars = nubBy (\a b -> tvId a == tvId b)

extractTyVarsFromTypes :: [Type] -> [TyVar]
extractTyVarsFromTypes = concatMap extractTyVars
