{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}

module Soma.Syntax.Parser where

import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import Data.Text qualified as T
import Maple.Ast (SyntaxKind (toRaw))
import Maple.Builder (runBuilderT)
import Maple.Builder qualified as M (BuilderT, finishNode, startNode, token)
import Maple.Cache (NodeCache)
import Maple.Green (GreenNode)
import Maple.Position (Range)
import Soma.Diagnostic (Diagnostic, Label (Label, labFile, labMessage, labRange), Severity (SError), mkDiag)
import Soma.File (SourceFile (srcContent))
import Soma.Syntax.Kind
import qualified Soma.Syntax.Lexer as L

data ParserState = ParserState
    { srcFile :: !SourceFile
    }

type Parser = M.BuilderT (L.LexerT (StateT ParserState IO))

label :: Range -> T.Text -> Parser Label
label range msg = do
    src <- lift $ lift $ gets srcFile
    pure Label{labRange = range, labMessage = msg, labFile = src}

mkError :: T.Text -> Label -> Diagnostic
mkError = mkDiag SError

bump :: Parser ()
bump = do
    (L.Token{tKind, tText}) <- lift L.next
    M.token (toRaw tKind) tText
    when (isTrivia tKind) bump

consume :: Kind -> Parser ()
consume kind = do
    t@L.Token{tKind} <- peek
    unless (tKind == kind) $ do
        let range = L.tRange t
        diag <-
            ( mkError ("expected " <> T.show kind <> ", but got " <> T.show tKind)
                <$> label range ("expected " <> T.show kind <> " here")
            )
        lift $ tell [diag]
    bump

peek :: Parser L.Token
peek = lift L.peekNonTrivial

peekNth :: Int -> Parser L.Token
peekNth n = lift $ L.peekNonTrivialNth n

incoming :: Parser Kind
incoming = L.tKind <$> peek

startNode :: Kind -> Parser ()
startNode = M.startNode . toRaw

parseRoot :: Parser ()
parseRoot = do
    startNode KRoot
    parseUntil KEof parseDecl
    M.finishNode
    pure ()

parseDecl :: Parser ()
parseDecl = do
    inc <- incoming
    case inc of
        KDefKw -> parseDef
        _ -> bump

parseDef :: Parser ()
parseDef = do
    startNode KDef
    consume KDefKw
    consume KIdent
    consume KLParen
    M.finishNode

parseUntil :: Kind -> Parser () -> Parser ()
parseUntil end parser = do
    inc <- incoming
    if inc == end
        then pure ()
        else (parser >> parseUntil end parser)

runParser :: SourceFile -> NodeCache -> Parser a -> IO ((GreenNode, NodeCache), [Diagnostic])
runParser src cache parser = do
    let s =
            ParserState
                { srcFile = src
                }
    let text = srcContent src
    ((nc, diag), _s') <- runStateT (L.runLexerT text $ runBuilderT cache parser) s
    pure (nc, diag)
