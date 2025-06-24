module Parsing.Types where

import Control.Monad.Error.Class (MonadError (throwError))
import Lexing.Lexer (Token (tokenKind, tokenValue), TokenKind (..))
import Parsing.Errors (ParsingError (InvalidTokenForType))
import Parsing.Parser (Parser, consume, consumeRelevant, next, parseSequence, peek)
import Typing.Types (Kind (KindStar), QualifiedType (Forall), TyVar (TypeVar), Type (TArrow, TUnresolved, TVar), arrayType, intType, strType, tupleType, boolType)

parseQualifiedType :: Parser QualifiedType
parseQualifiedType =
    Forall [] [] <$> parseType

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
    name <- consume TokenLowerIdentifier
    pure $ TypeVar (tokenValue name) KindStar

parseTypeConstructor :: Parser Type
parseTypeConstructor = do
    name <- consume TokenUpperIdentifier
    case tokenValue name of
        "Int" -> pure intType
        "String" -> pure strType
        "Bool" -> pure boolType
        other -> pure $ TUnresolved other
