module Parsing.Types where

import Control.Monad.Error.Class (MonadError (throwError))
import Data.List (nubBy)
import Lexing.Lexer (Token (tokenKind, tokenValue), TokenKind (..))
import Parsing.Errors (ParsingError (InvalidTokenForType))
import Parsing.Parser (Parser, consume, consumeRelevant, next, parseExhaustiveSequence, parseSequence, peek)
import Typing.Types (Constraint (Constraint), Kind (KindStar), QualifiedType (Forall), TyVar (TypeVar, tvId), Type (TArrow, TUnresolved, TVar), arrayType, boolType, extractTyVars, intType, strType, tupleType)

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
    initialType <- case tokenKind nextToken of
        TokenLeftParen -> do
            _ <- next
            types <- parseSequence TokenComma TokenRightParen parseType
            _ <- consume TokenRightParen
            case types of
                [singleType] -> pure singleType
                _ -> pure $ tupleType types
        TokenLeftBracket -> do
            _ <- next
            innerType <- parseType
            _ <- consume TokenRightBracket
            pure $ arrayType innerType
        TokenUpperIdentifier -> parseTypeConstructor
        TokenLowerIdentifier -> do
            _ <- next
            let name = tokenValue nextToken
            pure $ TVar (TypeVar name KindStar)
        _ -> throwError $ InvalidTokenForType nextToken
    incoming <- peek
    if tokenKind incoming == TokenRightArrow
        then do
            _ <- consumeRelevant TokenRightArrow
            TArrow initialType <$> parseType
        else pure initialType

parseTyVar :: Parser TyVar
parseTyVar = do
    nameTok <- consume TokenLowerIdentifier
    let name = (tokenValue nameTok)
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
    let name = (tokenValue varName)
    pure $ Constraint (tokenValue className) [TVar (TypeVar name KindStar)]

deduplicateTyVars :: [TyVar] -> [TyVar]
deduplicateTyVars = nubBy (\a b -> tvId a == tvId b)

extractTyVarsFromTypes :: [Type] -> [TyVar]
extractTyVarsFromTypes = concatMap extractTyVars
