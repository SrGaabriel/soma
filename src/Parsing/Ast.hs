module Parsing.Ast where

import qualified Data.Set as Set
import Lexing.Lexer (Token (tokenKind), TokenKind (..))
import Lexing.Position (Span (Span))
import Parsing.Bindings (parseBinding)
import Parsing.Errors (ParsingError (InvalidTokenForTopLevelDeclaration))
import Parsing.Parser (Parser, parseWithRecovery, peek, skipUntilSync, withRecovery, TokenStream)
import Syntax.Tree (Expr (ExprBindingDef, ExprRoot))
import Text.Megaparsec (ParseError)
import qualified Text.Megaparsec as MP
import Text.Megaparsec.Error (ErrorFancy (..), ParseError (..))
import Typing.Types (QualifiedType (Forall), intType)
import Data.List (nub)
import Data.Maybe (mapMaybe)

parse :: [Token] -> Either [ParsingError] Expr
parse tokens =
    case parseWithRecovery parser tokens of
        Right (root, errs) ->
            if null errs
                then Right root
                else Left (convertErrors errs)
        Left errs -> Left (convertErrors errs)
  where
    parser = do
        ExprRoot <$> someDeclarations

    convertErrors :: [ParseError TokenStream ParsingError] -> [ParsingError]
    convertErrors = nub . mapMaybe convertError

    convertError :: ParseError TokenStream ParsingError -> Maybe ParsingError
    convertError err = case err of
        FancyError _ errSet ->
            case Set.toList errSet of
                (ErrorCustom customErr : _) -> Just customErr
                _ -> Nothing
        TrivialError _ _unexpected _expected -> Nothing

someDeclarations :: Parser [Expr]
someDeclarations = do
    mtok <- MP.optional peek
    case mtok of
        Nothing -> pure []
        Just _ -> do
            decl <- recoverDeclaration
            rest <- someDeclarations
            pure (decl : rest)
  where
    recoverDeclaration = withRecovery parseDeclaration $ do
        skipUntilSync [TokenDef, TokenLayoutSeparator, TokenLayoutEnd]
        pure defaultDecl

    defaultDecl = ExprBindingDef "" (Forall [] [] intType) (ExprRoot []) False (Span 0 0)

parseDeclaration :: Parser Expr
parseDeclaration = do
    token <- peek
    case tokenKind token of
        TokenDef -> parseBinding True
        _ -> MP.customFailure $ InvalidTokenForTopLevelDeclaration token
