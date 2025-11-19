module Parsing.Ast where

import Data.List (nub)
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import qualified Debug.Trace as Debug
import Lexing.Lexer (Token (tokenKind), TokenKind (..))
import Lexing.Position (Span (Span))
import Parsing.Bindings (parseBinding)
import Parsing.DataTypes (parseDataType)
import Parsing.Errors (ParsingError (InvalidTokenForTopLevelDeclaration, UnexpectedParseFailure))
import Parsing.Parser (Parser, TokenStream, parseWithRecovery, peek, skipUntilSync, withRecovery)
import Syntax.Tree (Expr (ExprBindingDef, ExprRoot))
import Text.Megaparsec (ParseError)
import qualified Text.Megaparsec as MP
import Text.Megaparsec.Error (ErrorFancy (..), ParseError (..))
import Typing.Types (QualifiedType (Forall), intType)
import Parsing.Traits (parseTrait, parseInstance)

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
    Debug.traceM $ "Parsing declaration starting with token: " ++ show token
    case tokenKind token of
        TokenDef -> parseBinding True
        TokenData -> parseDataType
        TokenTrait -> parseTrait
        TokenInstance -> parseInstance
        _ -> MP.customFailure $ InvalidTokenForTopLevelDeclaration token
