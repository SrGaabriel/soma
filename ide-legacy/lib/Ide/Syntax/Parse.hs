module Ide.Syntax.Parse (
    parseSourceFile,
    parseIncremental,
    tokenToGreen,
    tokensToGreen,
    TreeBuilder,
    newTreeBuilder,
    startNode,
    finishNode,
    addToken,
    addError,
    finish,
) where

import Data.IORef
import Data.Text (Text)
import Data.Text qualified as T
import Ide.Vfs.Change (TextChange (..))
import Lexing.Lexer qualified as Soma
import Parsing.Cst.Parser qualified as CstParser
import Syntax.CST.GreenTree hiding (greenTokens)
import Syntax.CST.SyntaxKind

parseSourceFile :: GreenInterner -> Text -> IO GreenNode
parseSourceFile _interner source = do
    let (tokens, _lexErrors) = Soma.lexCode source

    case CstParser.parseCst tokens of
        Right greenTree -> pure greenTree
        Left _parseErr ->
            pure $ createFallbackTree tokens

createFallbackTree :: [Soma.Token] -> GreenNode
createFallbackTree tokens =
    let greenTokens = map tokenToGreenElement tokens
    in node (SK_Node NK_SOURCE_FILE) greenTokens
  where
    tokenToGreenElement tok =
        GreenTokenElement $ GreenToken (SK_Token (Soma.tokenKind tok)) (T.pack (Soma.tokenValue tok))

parseIncremental :: GreenInterner -> GreenNode -> TextChange -> Text -> IO GreenNode
parseIncremental interner _oldTree _change newSource = do
    parseSourceFile interner newSource

tokenToGreen :: GreenInterner -> Soma.Token -> IO GreenElement
tokenToGreen interner tok = do
    let kind = SK_Token (Soma.tokenKind tok)
        text = T.pack (Soma.tokenValue tok)
    internToken interner kind text

tokensToGreen :: GreenInterner -> [Soma.Token] -> IO [GreenElement]
tokensToGreen interner = mapM (tokenToGreen interner)

data TreeBuilder = TreeBuilder
    { tbInterner :: !GreenInterner
    , tbStack :: !(IORef [BuilderFrame])
    , tbChildren :: !(IORef [GreenElement])
    }

data BuilderFrame = BuilderFrame
    { bfKind :: !SyntaxKind
    , bfChildren :: ![GreenElement]
    }

newTreeBuilder :: GreenInterner -> IO TreeBuilder
newTreeBuilder interner =
    TreeBuilder interner
        <$> newIORef []
        <*> newIORef []

startNode :: TreeBuilder -> SyntaxKind -> IO ()
startNode builder kind = do
    currentChildren <- readIORef (tbChildren builder)
    stack <- readIORef (tbStack builder)
    let frame = BuilderFrame kind currentChildren
    writeIORef (tbStack builder) (frame : stack)
    writeIORef (tbChildren builder) []

finishNode :: TreeBuilder -> IO ()
finishNode builder = do
    stack <- readIORef (tbStack builder)
    case stack of
        [] -> return ()
        (frame : rest) -> do
            nodeChildren <- reverse <$> readIORef (tbChildren builder)
            greenNode <- internNode (tbInterner builder) (bfKind frame) nodeChildren
            writeIORef (tbStack builder) rest
            writeIORef (tbChildren builder) (GreenNodeElement greenNode : bfChildren frame)

addToken :: TreeBuilder -> GreenElement -> IO ()
addToken builder tok =
    modifyIORef' (tbChildren builder) (tok :)

addError :: TreeBuilder -> Text -> IO ()
addError builder txt = do
    errTok <- internToken (tbInterner builder) SK_Error txt
    addToken builder errTok

finish :: TreeBuilder -> IO GreenNode
finish builder = do
    stack <- readIORef (tbStack builder)
    mapM_ (const $ finishNode builder) stack

    rootChildren <- reverse <$> readIORef (tbChildren builder)

    case rootChildren of
        [GreenNodeElement root] -> return root
        _ -> internNode (tbInterner builder) (SK_Node NK_SOURCE_FILE) rootChildren
