{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Parsing.CstBuilder (
    CstParser,
    runCstParser,
    startNode,
    finishNode,
    abandonNode,
    addToken,
    cstConsume,
    cstConsumeAnyOf,
    cstPeek,
    cstTryPeek,
    cstTryPeekOrEOF,
    cstIsEOF,
    cstSatisfy,
    cstAnySingle,
    withNode,
    getGreenTree,
) where

import Control.Monad.State.Strict (StateT, gets, modify, runStateT)
import qualified Data.Set as Set
import qualified Data.Text as T
import Lexing.Lexer (Token (..))
import qualified Lexing.Lexer as Lexer
import Parsing.Errors (ParsingError (..))
import Parsing.Parser (TokenStream (..))
import Syntax.CST.GreenTree
import Syntax.CST.SyntaxKind
import Text.Megaparsec (Parsec)
import qualified Text.Megaparsec as MP

data BuilderFrame = BuilderFrame
    { bfKind :: !SyntaxKind
    , bfChildren :: ![GreenElement]
    }
    deriving (Show)

data CstBuilderState = CstBuilderState
    { cbsStack :: ![BuilderFrame]
    , cbsCurrentChildren :: ![GreenElement]
    }
    deriving (Show)

initialBuilderState :: CstBuilderState
initialBuilderState =
    CstBuilderState
        { cbsStack = []
        , cbsCurrentChildren = []
        }

type CstParser a = StateT CstBuilderState (Parsec ParsingError TokenStream) a

runCstParser :: CstParser a -> [Token] -> Either (MP.ParseErrorBundle TokenStream ParsingError) (a, GreenNode)
runCstParser parser tokens =
    case MP.runParser (runStateT parser initialBuilderState) "" (TokenStream tokens) of
        Left err -> Left err
        Right (result, finalState) ->
            let rootChildren = reverse (cbsCurrentChildren finalState)
                rootNode = node (SK_Node NK_SOURCE_FILE) rootChildren
            in Right (result, rootNode)

startNode :: SyntaxKind -> CstParser ()
startNode kind = do
    currentChildren <- gets cbsCurrentChildren
    stack <- gets cbsStack
    let frame = BuilderFrame kind currentChildren
    modify $ \s ->
        s
            { cbsStack = frame : stack
            , cbsCurrentChildren = []
            }

finishNode :: CstParser ()
finishNode = do
    stack <- gets cbsStack
    case stack of
        [] -> pure ()
        (frame : rest) -> do
            nodeChildren <- reverse <$> gets cbsCurrentChildren
            let greenNode = node (bfKind frame) nodeChildren
            modify $ \s ->
                s
                    { cbsStack = rest
                    , cbsCurrentChildren = GreenNodeElement greenNode : bfChildren frame
                    }

abandonNode :: CstParser ()
abandonNode = do
    stack <- gets cbsStack
    case stack of
        [] -> pure ()
        (frame : rest) -> do
            -- put children back where they were, discarding this node
            modify $ \s ->
                s
                    { cbsStack = rest
                    , cbsCurrentChildren = bfChildren frame
                    }

addToken :: Token -> CstParser ()
addToken tok = do
    let kind = SK_Token (Lexer.tokenKind tok)
        text = T.pack (tokenValue tok)
        greenTok = GreenToken kind text
    modify $ \s ->
        s{cbsCurrentChildren = GreenTokenElement greenTok : cbsCurrentChildren s}

cstConsume :: TokenKind -> CstParser Token
cstConsume kind = do
    tok <- MP.optional $ cstSatisfy (\t -> Lexer.tokenKind t == kind)
    case tok of
        Just t -> pure t
        Nothing -> do
            actual <- cstTryPeekOrEOF
            MP.customFailure
                $ ExpectedDifferentToken
                    { expectedTok = kind
                    , receivedTok = actual
                    }

cstConsumeAnyOf :: [TokenKind] -> CstParser Token
cstConsumeAnyOf kinds = do
    tok <- MP.optional $ cstSatisfy (\t -> Lexer.tokenKind t `elem` kinds)
    case tok of
        Just t -> pure t
        Nothing -> do
            actual <- cstTryPeekOrEOF
            MP.customFailure
                $ ExpectedOneOfTokens
                    { expectedTokens = kinds
                    , receivedToken = actual
                    }

cstSatisfy :: (Token -> Bool) -> CstParser Token
cstSatisfy f = do
    tok <- MP.token test Set.empty
    addToken tok
    pure tok
  where
    test t
        | f t = Just t
        | otherwise = Nothing

cstAnySingle :: CstParser Token
cstAnySingle = cstSatisfy (const True)

cstPeek :: CstParser Token
cstPeek = MP.lookAhead (MP.token Just Set.empty)

cstTryPeek :: CstParser (Maybe Token)
cstTryPeek = MP.optional cstPeek

cstTryPeekOrEOF :: CstParser Token
cstTryPeekOrEOF = do
    mtok <- cstTryPeek
    case mtok of
        Just tok -> pure tok
        Nothing -> pure $ Token TokenEOF "EOF" 0

cstIsEOF :: CstParser Bool
cstIsEOF = do
    mtok <- cstTryPeek
    case mtok of
        Nothing -> pure True
        Just tok | Lexer.tokenKind tok == TokenEOF -> pure True
        _ -> pure False

withNode :: SyntaxKind -> CstParser a -> CstParser a
withNode kind parser = do
    startNode kind
    result <- parser
    finishNode
    pure result

getGreenTree :: CstParser [GreenElement]
getGreenTree = reverse <$> gets cbsCurrentChildren
