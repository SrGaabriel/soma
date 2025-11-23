module Parsing.Ast where

import Data.List (nub)
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.Set as Set
import Lexing.Lexer (Token (..), TokenKind (..))
import Parsing.Bindings (parseBinding)
import Parsing.DataTypes (parseDataType)
import Parsing.Errors (ParsingError (..))
import Parsing.Imports (parseImport)
import Parsing.Intrinsics (parseIntrinsic)
import Parsing.Parser (Parser, TokenStream, isEOF, parseWithRecovery, peek, recordError, skipUntilSync)
import Parsing.Traits (parseInstance, parseTrait)
import Syntax.Tree (Expr (ExprRoot))
import Text.Megaparsec (
    ErrorItem (Label, Tokens),
    MonadParsec (observing),
    ParseError,
 )
import qualified Text.Megaparsec as MP
import Text.Megaparsec.Error (ErrorFancy (..), ParseError (..))
import Data.Maybe (mapMaybe)
import Utils.Lists (hardLast)

parse :: [Token] -> Either [ParsingError] ([ParsingError], Expr)
parse tokens =
    case parseWithRecovery parser tokens of
        Right (root, errs) -> Right (convertErrors errs, root)
        Left errs -> Left (convertErrors errs)
  where
    parser = do
        ExprRoot <$> someDeclarations
    convertErrors :: [ParseError TokenStream ParsingError] -> [ParsingError]
    convertErrors = nub . map convertError
    convertError :: ParseError TokenStream ParsingError -> ParsingError
    convertError err = case err of
        FancyError _pos errSet ->
            case Set.toList errSet of
                (ErrorCustom customErr : _) -> customErr
                _ -> UnexpectedParseFailure "Unknown fancy error" 0
        TrivialError _pos unexpected expected' ->
            case (unexpected, Set.toList expected') of
                (Just (Tokens (tok :| _)), expectedItems) ->
                    case extractExpectedTokens expectedItems of
                        [single] -> ExpectedDifferentToken single tok
                        multiple@(_ : _) -> ExpectedOneOfTokens multiple tok
                        [] -> UnexpectedToken tok

                (Just MP.EndOfInput, expectedItems) ->
                    case extractExpectedTokens expectedItems of
                        [single] -> ExpectedDifferentToken single (Token TokenEOF "" 0)
                        multiple@(_ : _) -> ExpectedOneOfTokens multiple (Token TokenEOF "" 0)
                        [] -> EndOfInput $ hardLast tokens

                (Just (Label _), _) -> UnexpectedParseFailure "Unexpected label" 0

                (Nothing, expectedItems) ->
                    case extractExpectedTokens expectedItems of
                        [single] -> ExpectedDifferentToken single (Token TokenEOF "" 0)
                        multiple@(_ : _) -> ExpectedOneOfTokens multiple (Token TokenEOF "" 0)
                        [] -> UnexpectedParseFailure "Parse error with no details" 0

    extractExpectedTokens :: [ErrorItem Token] -> [TokenKind]
    extractExpectedTokens = mapMaybe extractTokenKind
      where
        extractTokenKind (Tokens (tok :| _)) = Just (tokenKind tok)
        extractTokenKind (Label _) = Nothing
        extractTokenKind MP.EndOfInput = Just TokenEOF

someDeclarations :: Parser [Expr]
someDeclarations = go []
  where
    go acc = do
        atEnd <- isEOF
        if atEnd
            then pure (reverse acc)
            else do
                mtok <- MP.optional peek
                case mtok of
                    Nothing -> pure (reverse acc)
                    Just _ -> do
                        mdecl <- recoverDeclaration
                        case mdecl of
                            Just decl -> go (decl : acc)
                            Nothing -> go acc
    recoverDeclaration :: Parser (Maybe Expr)
    recoverDeclaration = do
        result <- observing parseDeclaration
        case result of
            Right decl -> pure (Just decl)
            Left err -> do
                recordError err
                skipUntilSync syncTokens
                pure Nothing
    syncTokens =
        [ TokenDef
        , TokenData
        , TokenTrait
        , TokenInstance
        , TokenIntrinsic
        , TokenImport
        , TokenLayoutSeparator
        , TokenLayoutEnd
        ]

parseDeclaration :: Parser Expr
parseDeclaration = do
    token <- peek
    case tokenKind token of
        TokenDef -> parseBinding True
        TokenData -> parseDataType
        TokenTrait -> parseTrait
        TokenInstance -> parseInstance
        TokenIntrinsic -> parseIntrinsic
        TokenImport -> parseImport
        _ -> MP.customFailure $ InvalidTokenForTopLevelDeclaration token
