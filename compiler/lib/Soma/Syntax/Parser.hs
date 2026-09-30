module Soma.Syntax.Parser where

import Control.Monad.State.Strict
import qualified Maple.Builder as M (BuilderT, startNode, finishNode, token)
import Soma.Syntax.Kind
import Soma.Syntax.Lexer (LexerT, next)

data ParserState = ParserState
    {
    }

type Parser a = M.BuilderT (LexerT (StateT ParserState IO)) a

bump :: Parser ()
bump = do
    inc <- lift next
    M.token inc 
    pure ()

parseRoot :: Parser ()
parseRoot = do
    startNode tRoot
    inc <- lift next
    token
    finishNode
    pure ()
