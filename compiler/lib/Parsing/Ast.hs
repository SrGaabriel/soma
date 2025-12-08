module Parsing.Ast where

import Control.Monad (void, when)
import Control.Monad.State.Strict (evalStateT)
import Data.List (nub)
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import Lexing.Lexer (Token (..), TokenKind (..))
import Lexing.Position (Located)
import Parsing.Attributes (parseAttributes)
import Parsing.Bindings (parseBindingWithAttributes)
import Parsing.DataTypes (parseDataTypeWithAttributes, parseStructWithAttributes)
import Parsing.Errors (ParsingError (..))
import Parsing.Imports (parseExport, parseImport)
import Parsing.Intrinsics (parseIntrinsic)
import Parsing.Parser (Parser, TokenStream (..), anySingle, consume, getErrors, initialErrorState, isEOF, peek, recordError, skipUntilSync, tryPeek)
import Parsing.Traits (parseInstance, parseTrait)
import Syntax.Tree (Attribute, Expr (ExprRoot))
import Text.Megaparsec (
    ErrorItem (Label, Tokens),
    MonadParsec (observing),
    ParseError,
    bundleErrors,
    getOffset,
    runParser,
 )
import qualified Text.Megaparsec as MP
import Text.Megaparsec.Error (ErrorFancy (..), ParseError (..))
import Utils.Lists (hardLast)

parse :: [Token] -> Either [ParsingError] ([ParsingError], Expr)
parse tokens =
    case runParser (evalStateT parser initialErrorState) "" (TokenStream tokens) of
        Left bundle ->
            Left (nub $ extractErrorsFromBundle bundle tokens)
        Right (result, recoveredErrors) ->
            Right (nub $ map (convertError tokens) recoveredErrors, result)
  where
    parser = do
        decls <- someDeclarations
        errors <- getErrors
        pure (ExprRoot decls, errors)

extractErrorsFromBundle :: MP.ParseErrorBundle TokenStream ParsingError -> [Token] -> [ParsingError]
extractErrorsFromBundle bundle tokens =
    map (convertError tokens) (NE.toList $ bundleErrors bundle)

convertError :: [Token] -> ParseError TokenStream ParsingError -> ParsingError
convertError tokens err = case err of
    FancyError _pos errSet ->
        case Set.toList errSet of
            (ErrorCustom customErr : _) -> customErr
            _ -> Debug
    TrivialError pos unexpected expected' ->
        case (unexpected, Set.toList expected') of
            (Just (Tokens (tok :| _)), expectedItems) ->
                case extractExpectedTokens expectedItems of
                    [single] -> ExpectedDifferentToken single tok
                    multiple@(_ : _) -> ExpectedOneOfTokens multiple tok
                    [] -> UnexpectedToken tok
            (Just MP.EndOfInput, expectedItems) ->
                let eofToken = if null tokens then Token TokenEOF "" 0 else hardLast tokens
                in case extractExpectedTokens expectedItems of
                    [single] -> ExpectedDifferentToken single eofToken
                    multiple@(_ : _) -> ExpectedOneOfTokens multiple eofToken
                    [] -> EndOfInput eofToken
            (Just (Label _), _) ->
                let tok = if pos > 0 && pos <= length tokens then tokens !! (pos - 1) else Token TokenEOF "" 0
                in UnexpectedParseFailure tok "Unexpected label"
            (Nothing, expectedItems) ->
                let tok = if pos > 0 && pos <= length tokens then tokens !! (pos - 1) else Token TokenEOF "" 0
                in case extractExpectedTokens expectedItems of
                    [single] -> ExpectedDifferentToken single tok
                    multiple@(_ : _) -> ExpectedOneOfTokens multiple tok
                    [] -> UnexpectedParseFailure tok "Parse error with no details"
  where
    extractExpectedTokens :: [ErrorItem Token] -> [TokenKind]
    extractExpectedTokens = mapMaybe extractTokenKind
    extractTokenKind (Tokens (tok :| _)) = Just (tokenKind tok)
    extractTokenKind (Label _) = Nothing
    extractTokenKind MP.EndOfInput = Just TokenEOF

someDeclarations :: Parser [Expr]
someDeclarations = go []
  where
    go acc = do
        skipLayoutSeparators
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

    skipLayoutSeparators :: Parser ()
    skipLayoutSeparators = do
        mtok <- tryPeek
        case mtok of
            Just Token{tokenKind = TokenLayoutSeparator} -> do
                void $ consume TokenLayoutSeparator
                skipLayoutSeparators
            _ -> pure ()

    recoverDeclaration :: Parser (Maybe Expr)
    recoverDeclaration = do
        startPos <- getOffset
        result <- observing parseDeclaration
        case result of
            Right decl -> pure (Just decl)
            Left err -> do
                recordError err
                skipUntilSync syncTokens
                endPos <- getOffset
                when (startPos == endPos) $ do
                    void $ MP.optional anySingle
                pure Nothing

    syncTokens =
        [ TokenDef
        , TokenAt
        , TokenData
        , TokenStruct
        , TokenTrait
        , TokenInstance
        , TokenIntrinsic
        , TokenImport
        , TokenExport
        , TokenLayoutSeparator
        , TokenLayoutEnd
        ]

parseDeclaration :: Parser Expr
parseDeclaration = do
    attrs <- parseAttributes
    parseDeclarationWithAttributes attrs

parseDeclarationWithAttributes :: [Located Attribute] -> Parser Expr
parseDeclarationWithAttributes attrs = do
    token <- peek
    case tokenKind token of
        TokenDef -> parseBindingWithAttributes True attrs
        TokenData -> parseDataTypeWithAttributes attrs
        TokenStruct -> parseStructWithAttributes attrs
        TokenTrait -> parseTrait
        TokenInstance -> parseInstance
        TokenIntrinsic -> parseIntrinsic
        TokenImport -> parseImport
        TokenExport -> parseExport
        _ -> MP.customFailure $ InvalidTokenForTopLevelDeclaration token
