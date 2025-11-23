module Parsing.Ast where

import Data.List (nub)
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import Lexing.Lexer (Token (tokenKind), TokenKind (..))
import Lexing.Position (Span (Span))
import Parsing.Bindings (parseBinding)
import Parsing.DataTypes (parseDataType)
import Parsing.Errors (ParsingError (InvalidTokenForTopLevelDeclaration, UnexpectedParseFailure))
import Parsing.Imports (parseImport)
import Parsing.Intrinsics (parseIntrinsic)
import Parsing.Parser (Parser, TokenStream, isEOF, parseWithRecovery, peek, skipUntilSync, withRecovery)
import Parsing.Traits (parseInstance, parseTrait)
import Syntax.Tree (Expr (ExprBindingDef, ExprRoot))
import Text.Megaparsec (ParseError)
import qualified Text.Megaparsec as MP
import Text.Megaparsec.Error (ErrorFancy (..), ParseError (..))
import Typing.Types (QualifiedType (Forall), intType)

parse :: [Token] -> Either [ParsingError] ([ParsingError], Expr)
parse tokens =
    case parseWithRecovery parser tokens of
        Right (root, errs) -> Right (convertErrors errs, root)
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
                _ -> Just $ UnexpectedParseFailure "Unknown fancy error"
        TrivialError pos unexpected expected ->
            Just
                $ UnexpectedParseFailure
                $ "Parse error at "
                    ++ show pos
                    ++ ": unexpected "
                    ++ show unexpected
                    ++ ", expected "
                    ++ show expected

-- FIXED: Use tail-recursive accumulator pattern instead of cons recursion
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
                        decl <- recoverDeclaration
                        go (decl : acc)

    recoverDeclaration = withRecovery parseDeclaration $ do
        skipUntilSync syncTokens
        pure defaultDecl

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

    defaultDecl = ExprBindingDef "" (Forall [] [] intType) (ExprRoot []) False (Span 0 0)

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
