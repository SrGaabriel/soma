module Parsing.Types where

import Control.Monad.Error.Class (MonadError (throwError))
import Lexing.Lexer (Token (tokenKind, tokenValue), TokenKind (..))
import Parsing.Errors (ParsingError (InvalidTokenForType))
import Parsing.Parser (Parser, consume, consumeRelevant, next, parseSequence, peek)
import Typing.Types (Kind (KindStar), QualifiedType (Forall), TyConstructor (TypeConstructor), TyVar (TypeVar), Type (TArrow, TConstructor, TVar), arrayType, tupleType)

parseQualifiedType :: Parser QualifiedType
parseQualifiedType = do
    typ <- parseType
    pure $ Forall [] [] typ

parseType :: Parser Type
parseType = do
    nextToken <- next
    initialType <- case tokenKind nextToken of
        TokenLeftParen -> do
            types <- parseSequence TokenComma TokenRightParen (parseType)
            _ <- consume TokenRightParen
            case types of
                [singleType] -> pure singleType
                _ -> pure $ tupleType types
        TokenLeftBracket -> do
            innerType <- parseType
            _ <- consume TokenRightBracket
            pure $ arrayType innerType
        TokenUpperIdentifier -> do
            let name = tokenValue nextToken
            pure $ TConstructor (TypeConstructor name KindStar)
        TokenLowerIdentifier -> do
            let name = tokenValue nextToken
            pure $ TVar (TypeVar name KindStar)
        _ -> throwError $ InvalidTokenForType nextToken
    incoming <- peek
    if tokenKind incoming == TokenRightArrow
        then do
            _ <- consumeRelevant TokenRightArrow
            returnType <- parseType
            pure $ TArrow initialType returnType
        else pure initialType

parseTyVar :: Parser TyVar
parseTyVar = do
    name <- consume TokenLowerIdentifier
    pure $ TypeVar (tokenValue name) KindStar
