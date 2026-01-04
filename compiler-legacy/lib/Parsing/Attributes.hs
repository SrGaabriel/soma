module Parsing.Attributes (parseAttributes) where

import Lexing.Lexer (Token (..), TokenKind (..), tokenSpan)
import Lexing.Position (Located (..))
import Parsing.Errors (ParsingError (..))
import Parsing.Parser (Parser, consume, parseCommaSeparatedUntil, tryPeek)
import Syntax.Tree (Attribute (..))
import qualified Text.Megaparsec as MP

parseAttributes :: Parser [Located Attribute]
parseAttributes = concat <$> MP.many parseAttributeBlock

parseAttributeBlock :: Parser [Located Attribute]
parseAttributeBlock = do
    _ <- consume TokenAt
    _ <- consume TokenLeftBracket
    attrs <- parseCommaSeparatedUntil TokenRightBracket parseAttribute
    _ <- consume TokenRightBracket
    pure attrs

parseAttribute :: Parser (Located Attribute)
parseAttribute = do
    nameTok <- consume TokenLowerIdentifier
    let name = tokenValue nameTok
    let span' = tokenSpan nameTok
    case name of
        "inline" -> pure $ Located span' AttrInline
        "noinline" -> pure $ Located span' AttrNoInline
        "deprecated" -> do
            msg <- MP.optional parseStringArg
            pure $ Located span' (AttrDeprecated msg)
        "extern" -> Located span' . AttrExtern <$> parseStringArg
        _ -> MP.customFailure $ UnknownAttribute nameTok

parseStringArg :: Parser String
parseStringArg = do
    mtok <- tryPeek
    case mtok of
        Just Token{tokenKind = TokenString s} -> do
            _ <- consume (TokenString s)
            pure s
        _ -> MP.empty
