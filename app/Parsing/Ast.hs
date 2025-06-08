module Parsing.Ast where

import Lexing.Lexer (Token (tokenKind), TokenKind (TokenNewline, TokenIdentifier))
import Parsing.Errors (ParsingError (UnexpectedToken))
import Syntax.Tree (Expr (ExprRoot))
import Parsing.Parser (parseExhaustiveSequence, Parser (runParser, Parser), next, peek)
import Parsing.Bindings (parseBinding)

parse :: [Token] -> Either ParsingError Expr
parse tokens = do
    (root, _) <- runParser parser tokens
    pure root
  where
    parser = do
        declarations <- parseExhaustiveSequence TokenNewline parseDeclaration
        pure $ ExprRoot declarations

parseDeclaration :: Parser Expr
parseDeclaration = do
    token <- peek
    case tokenKind token of
        TokenIdentifier -> parseBinding
        TokenNewline -> next >> parseDeclaration
        _ -> Parser $ \_ -> Left $ UnexpectedToken token