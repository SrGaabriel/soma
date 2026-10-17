{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}

module Soma.Syntax.Parser where

import Blammo.Logging
import Blammo.Logging.Setup (LoggingT, runLoggerLoggingT)
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import Data.Text qualified as T
import Maple.Ast (SyntaxKind (toRaw))
import Maple.Builder (runBuilderT)
import Maple.Builder qualified as M (BuilderT, finishNode, startNode, token)
import Maple.Cache (NodeCache)
import Maple.Green (GreenNode)
import Maple.Position (Pos, Range (Range), posRowCol)
import Soma.Diagnostic (Diagnostic, Label (Label, labFile, labMessage, labRange), Severity (SError), addSecondary, mkDiag)
import Soma.File (SourceFile (srcContent))
import Soma.Print (Pretty (pretty))
import Soma.Syntax.Kind
import Soma.Syntax.Lexer (Token (Token))
import Soma.Syntax.Lexer qualified as L
import Soma.Syntax.TokenSet (TokenSet, member, tokenSet)

data ParserState = ParserState
    { srcFile :: !SourceFile
    , psFuel :: !Int
    , psPrevEnd :: !Pos
    , psTokenIndex :: !Int
    , psLastErrorAt :: !Int
    }

type Parser = M.BuilderT (L.LexerT (StateT ParserState (LoggingT IO)))

fuelLimit :: Int
fuelLimit = 256

anchors :: TokenSet
anchors = tokenSet [KEof, KDefKw]

declFirst :: TokenSet
declFirst = tokenSet [KDefKw]

binderFirst :: TokenSet
binderFirst = tokenSet [KLParen, KLBrace]

typeFirst :: TokenSet
typeFirst = tokenSet [KIdent]

getsPS :: (ParserState -> a) -> Parser a
getsPS = lift . lift . gets

modifyPS :: (ParserState -> ParserState) -> Parser ()
modifyPS = lift . lift . modify'

label :: Range -> T.Text -> Parser Label
label range msg = do
    src <- getsPS srcFile
    pure Label{labRange = range, labMessage = msg, labFile = src}

mkError :: T.Text -> Label -> Diagnostic
mkError = mkDiag SError

peek :: Parser Token
peek = peekNth 0

peekNth :: Int -> Parser Token
peekNth n = do
    t <- lift $ L.peekNonTrivialNth n
    fuel <- getsPS psFuel
    when (fuel <= 0)
        $ error ("parser made no progress after " <> show fuelLimit <> " lookaheads at " <> show t)
    modifyPS (\s -> s{psFuel = fuel - 1})
    pure t

incoming :: Parser Kind
incoming = L.tKind <$> peek

at :: Kind -> Parser Bool
at k = (== k) <$> incoming

atAny :: TokenSet -> Parser Bool
atAny ks = (`member` ks) <$> incoming

eatTrivia :: Parser ()
eatTrivia = do
    Token{tKind, tText} <- lift L.peek
    when (isTrivia tKind) $ do
        void (lift L.next)
        M.token (toRaw tKind) tText
        eatTrivia

bump :: Parser Token
bump = do
    eatTrivia
    t@Token{tKind, tText} <- lift L.next
    unless (tKind == KEof) $ do
        M.token (toRaw tKind) tText
        let Range _ end = L.tRange t
        modifyPS
            ( \s ->
                s
                    { psFuel = fuelLimit
                    , psPrevEnd = end
                    , psTokenIndex = psTokenIndex s + 1
                    }
            )
    pure t

bump_ :: Parser ()
bump_ = void bump

startNode :: Kind -> Parser ()
startNode k = eatTrivia >> M.startNode (toRaw k)

expect :: Kind -> Parser Bool
expect kind = do
    t <- peek
    logDebug $ "expect" :# ["expected" .= pretty kind, "got" .= pretty (L.tKind t)]
    if L.tKind t == kind
        then True <$ bump_
        else False <$ errorExpected [pretty kind]

expectClosing :: Kind -> Token -> Parser ()
expectClosing close open = do
    found <- at close
    if found
        then bump_
        else do
            unclosed <- label (L.tRange open) ("unclosed " <> pretty (L.tKind open))
            errorExpectedWith (addSecondary unclosed) [pretty close]

describe :: Token -> T.Text
describe Token{tKind, tText} = case tKind of
    KIdent -> "identifier '" <> tText <> "'"
    KNumber -> "number " <> tText
    KUnknown -> "unknown character '" <> tText <> "'"
    _ -> pretty tKind

oneOf :: [T.Text] -> T.Text
oneOf [] = "nothing"
oneOf [x] = x
oneOf [x, y] = x <> " or " <> y
oneOf xs = T.intercalate ", " (init xs) <> ", or " <> last xs

report :: Int -> Diagnostic -> Parser ()
report index diag = do
    lastAt <- getsPS psLastErrorAt
    unless (index == lastAt) $ do
        modifyPS (\s -> s{psLastErrorAt = index})
        lift $ tell [diag]

missingRange :: Token -> Parser Range
missingRange t = do
    prevEnd <- getsPS psPrevEnd
    src <- srcContent <$> getsPS srcFile
    let found@(Range start _) = L.tRange t
        line p = fst (posRowCol src p)
    pure
        $ if L.tKind t /= KEof && line start == line prevEnd
            then found
            else Range prevEnd prevEnd

errorExpected :: [T.Text] -> Parser ()
errorExpected = errorExpectedWith id

errorExpectedWith :: (Diagnostic -> Diagnostic) -> [T.Text] -> Parser ()
errorExpectedWith extend expected = do
    t <- peek
    range <- missingRange t
    lab <- label range ("expected " <> oneOf expected)
    index <- getsPS psTokenIndex
    report index $ extend $ mkError ("expected " <> oneOf expected <> ", found " <> describe t) lab

skipWithError :: [T.Text] -> TokenSet -> Parser ()
skipWithError expected stop = do
    first <- peek
    index <- getsPS psTokenIndex
    startNode KError
    let Range start _ = L.tRange first
        go end = do
            stopped <- atAny (stop <> anchors)
            if stopped
                then pure end
                else do
                    t <- bump
                    let Range _ end' = L.tRange t
                    go end'
    end <- go start
    M.finishNode
    lab <- label (Range start end) ("expected " <> oneOf expected)
    report index $ mkError ("expected " <> oneOf expected <> ", found " <> describe first) lab

errRecover :: [T.Text] -> TokenSet -> Parser ()
errRecover expected recovery = do
    meaningful <- atAny (recovery <> anchors)
    if meaningful
        then errorExpected expected
        else skipWithError expected recovery

list :: Kind -> TokenSet -> TokenSet -> [T.Text] -> Parser () -> Parser ()
list end first recovery expected item = go
  where
    stop = tokenSet [end] <> recovery <> anchors
    go = do
        inc <- incoming
        if
            | inc == end -> pure ()
            | inc `member` first -> item >> go
            | inc `member` stop -> pure ()
            | otherwise -> skipWithError expected (first <> stop) >> go

parseRoot :: Parser ()
parseRoot = do
    M.startNode (toRaw KRoot)
    list KEof declFirst mempty ["declaration"] parseDecl
    eatTrivia
    M.finishNode

parseDecl :: Parser ()
parseDecl = do
    inc <- incoming
    case inc of
        KDefKw -> parseDef
        _ -> errRecover ["declaration"] mempty

parseDef :: Parser ()
parseDef = do
    startNode KDef
    bump_
    _ <- expect KIdent
    list KColon binderFirst (typeFirst <> tokenSet [KColonEq]) ["binder", pretty KColon] parseBinder
    _ <- expect KColon
    parseType (tokenSet [KColonEq])
    _ <- expect KColonEq
    parseExpr mempty
    M.finishNode

parseExpr :: TokenSet -> Parser ()
parseExpr recovery = do
    inc <- incoming
    case inc of
        KIdent -> bump_
        KNumber -> bump_
        KLBrace -> parseBlock
        _ -> errRecover ["expression"] recovery

parseBlock :: Parser ()
parseBlock = do
    open <- peek
    startNode KBlock
    bump_
    parseBlockBody
    expectClosing KRBrace open
    M.finishNode

parseBlockBody :: Parser ()
parseBlockBody = do
    done <- atAny (tokenSet [KRBrace] <> anchors)
    unless done $ skipWithError [pretty KRBrace] (tokenSet [KRBrace])

parseBinder :: Parser ()
parseBinder = do
    open <- peek
    let (kind, close) = case L.tKind open of
            KLParen -> (KExBinder, KRParen)
            _ -> (KClBinder, KRBrace)
    startNode kind
    bump_
    _ <- expect KIdent
    _ <- expect KColon
    parseType (tokenSet [close])
    expectClosing close open
    M.finishNode

parseType :: TokenSet -> Parser ()
parseType recovery = do
    inc <- incoming
    if inc `member` typeFirst
        then startNode KType >> bump_ >> M.finishNode
        else errRecover ["type"] recovery

runParser :: Logger -> SourceFile -> NodeCache -> Parser a -> IO ((GreenNode, NodeCache), [Diagnostic])
runParser logger src cache parser = do
    let s =
            ParserState
                { srcFile = src
                , psFuel = fuelLimit
                , psPrevEnd = 0
                , psTokenIndex = 0
                , psLastErrorAt = -1
                }
    let text = srcContent src
    ((nc, diag), _s') <- runLoggerLoggingT logger $ runStateT (L.runLexerT text $ runBuilderT cache parser) s
    pure (nc, diag)
