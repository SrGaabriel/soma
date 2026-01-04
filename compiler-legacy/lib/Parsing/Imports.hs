module Parsing.Imports (parseImport, parseExport) where

import Control.Monad (unless)
import Data.List (intercalate)
import Lexing.Lexer (Token (tokenValue), TokenKind (..), tokenSpan)
import Lexing.Position (Span (..))
import Parsing.Atoms (parseModuleName)
import Parsing.Errors (ParsingError (UnexpectedToken))
import Parsing.Parser (Parser, consume, consumeAnyOf, parseBracedSequence, parseSequence)
import Syntax.Tree (Expr (..))
import qualified Text.Megaparsec as MP

parseImport :: Parser Expr
parseImport = do
    importToken <- consume TokenImport
    moduleNameSegments <- parseModuleName
    separator <- consume TokenVarSymbol
    unless (tokenValue separator == ".") $ do
        MP.customFailure $ UnexpectedToken separator

    _ <- consume TokenLeftBraces
    imports <-
        parseSequence
            TokenComma
            TokenRightBraces
            ( do
                nameToken <-
                    consumeAnyOf
                        [ TokenLowerIdentifier
                        , TokenUpperIdentifier
                        , TokenVarSymbol
                        ]
                pure $ tokenValue nameToken
            )
    _ <- consume TokenRightBraces

    let moduleName = intercalate "/" moduleNameSegments
    let Span importStart _ = tokenSpan importToken
    let importEnd = importStart + length moduleNameSegments
    pure $ ExprImport moduleName imports (Span importStart importEnd)

parseExport :: Parser Expr
parseExport = do
    exportToken <- consume TokenExport
    _ <- consume TokenLeftBraces
    exports <-
        parseBracedSequence
            ( do
                nameToken <-
                    consumeAnyOf
                        [ TokenLowerIdentifier
                        , TokenUpperIdentifier
                        , TokenVarSymbol
                        ]
                pure $ tokenValue nameToken
            )
    closeBrace <- consume TokenRightBraces

    let Span exportStart _ = tokenSpan exportToken
    let Span _ exportEnd = tokenSpan closeBrace
    pure $ ExprExport exports (Span exportStart exportEnd)
