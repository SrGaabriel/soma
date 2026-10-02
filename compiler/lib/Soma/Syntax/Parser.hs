{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE Strict #-}

module Soma.Syntax.Parser where

import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import Data.Text (Text)
import Maple.Ast (fromRaw)
import Maple.Builder (runBuilderT)
import Maple.Builder qualified as M (BuilderT, finishNode, startNode, token)
import Maple.Cache (NodeCache)
import Maple.Green (GreenNode)
import Soma.Diagnostic (Diagnostic)
import Soma.Syntax.Kind
import Soma.Syntax.Lexer (LexerT, Token (Token, tKind, tText), next, peek, runLexerT)

data ParserState = ParserState
    {
    }

type Parser = M.BuilderT (LexerT (StateT ParserState (WriterT [Diagnostic] IO)))

bump :: Parser ()
bump = do
    (Token{tKind, tText}) <- lift next
    M.token tKind tText
    pure ()

incoming :: Parser Kind
incoming = (fromRaw . tKind) <$> (lift peek)

eatTrivia :: Parser ()
eatTrivia = do
    inc <- incoming
    when (isTrivia inc) (bump *> eatTrivia)

parseRoot :: Parser ()
parseRoot = do
    M.startNode kRoot
    parseUntil KEof parseDecl
    M.finishNode
    pure ()

parseDecl :: Parser ()
parseDecl = bump

parseUntil :: Kind -> Parser () -> Parser ()
parseUntil end parser = do
    inc <- incoming
    if inc == end
        then pure ()
        else (parser >> parseUntil end parser)

runParser :: Text -> NodeCache -> Parser a -> IO ((GreenNode, NodeCache), [Diagnostic])
runParser text cache parser = do
    let s =
            ParserState
                {
                }
    (((nc, diag), _s'), diag') <- runWriterT $ runStateT (runLexerT text $ runBuilderT cache parser) s
    pure (nc, diag <> diag')
