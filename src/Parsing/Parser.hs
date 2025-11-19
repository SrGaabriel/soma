{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Parsing.Parser where

import Control.Monad (void, when)
import Control.Monad.State
import Data.Functor (($>))
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Lexing.Lexer (Token (..), TokenKind (..), tokenKind)
import Parsing.Errors (ParsingError (..))
import Text.Megaparsec hiding (Token, anySingle, parse, satisfy, tokens, withRecovery)
import qualified Text.Megaparsec as MP

newtype TokenStream = TokenStream {unTokenStream :: [Token]}
    deriving (Eq, Ord)

instance Stream TokenStream where
    type Token TokenStream = Token
    type Tokens TokenStream = TokenStream
    tokenToChunk _ t = TokenStream [t]
    tokensToChunk _ = TokenStream
    chunkToTokens _ = unTokenStream
    chunkLength _ = length . unTokenStream
    chunkEmpty _ = null . unTokenStream
    take1_ (TokenStream []) = Nothing
    take1_ (TokenStream (t : ts)) = Just (t, TokenStream ts)
    takeN_ n (TokenStream s)
        | n <= 0 = Just (TokenStream [], TokenStream s)
        | null s = Nothing
        | otherwise = let (pre, post) = splitAt n s in Just (TokenStream pre, TokenStream post)
    takeWhile_ f (TokenStream s) = let (pre, post) = span f s in (TokenStream pre, TokenStream post)

instance VisualStream TokenStream where
    showTokens _ = unwords . map (show . tokenKind) . NE.toList

instance TraversableStream TokenStream where
    reachOffset offset pstate =
        let tokens = unTokenStream (pstateInput pstate)
            (pre, post) = splitAt (offset - pstateOffset pstate) tokens
            newOffset = pstateOffset pstate + length pre
            newState =
                pstate
                    { pstateOffset = newOffset
                    , pstateInput = TokenStream post
                    }
            line = case post of
                [] -> "<end of input>"
                (t : _) -> "at " ++ show (tokenKind t)
        in (Just line, newState)

type Parser = StateT ParserState (Parsec ParsingError TokenStream)

data ParserState = ParserState
    { accumulatedErrors :: [ParseError TokenStream ParsingError]
    , errorCount :: Int
    }

initialParserState :: ParserState
initialParserState = ParserState [] 0

recordError :: ParseError TokenStream ParsingError -> Parser ()
recordError err = modify $ \s ->
    s
        { accumulatedErrors = err : accumulatedErrors s
        , errorCount = errorCount s + 1
        }

withRecovery :: Parser a -> Parser a -> Parser a
withRecovery parser recovery = do
    observing parser >>= \case
        Right result -> pure result
        Left err -> do
            recordError err
            recovery

skipUntilSync :: [TokenKind] -> Parser ()
skipUntilSync syncTokens = void $ MP.manyTill skipOne (lookAhead syncPoint <|> eof)
  where
    syncPoint = MP.choice [void (satisfy (\t -> tokenKind t `elem` syncTokens))]
    skipOne = do
        tok <- anySingle
        when (tokenKind tok == TokenLayoutStart)
            $ void
            $ MP.manyTill anySingle (satisfy (\t -> tokenKind t == TokenLayoutEnd))

recoverStatement :: Parser a -> a -> Parser a
recoverStatement parser defaultValue =
    withRecovery parser (skipUntilSync syncTokens $> defaultValue)
  where
    syncTokens =
        [ TokenLayoutSeparator
        , TokenLayoutEnd
        , TokenLet
        , TokenData
        ]

parseWithRecovery :: Parser a -> [Token] -> Either [ParseError TokenStream ParsingError] (a, [ParseError TokenStream ParsingError])
parseWithRecovery parser tokens =
    case runParser (runStateT parser initialParserState) "" (TokenStream tokens) of
        Left bundle ->
            let errs = NE.toList (MP.bundleErrors bundle)
            in Left errs
        Right (result, st) ->
            let allErrors = reverse (accumulatedErrors st)
            in Right (result, allErrors)

satisfy :: (Token -> Bool) -> Parser Token
satisfy f = token test Set.empty
  where
    test t
        | f t = Just t
        | otherwise = Nothing

unrecoverableConsume :: TokenKind -> Parser Token
unrecoverableConsume kind = do
    tok <- optional $ satisfy (\t -> tokenKind t == kind)
    case tok of
        Just t -> pure t
        Nothing -> do
            actual <- tryPeekOrEOF
            MP.customFailure
                $ ExpectedDifferentToken
                    { expected = kind
                    , received = actual
                    }

consume :: TokenKind -> Parser Token
consume kind = withRecovery (unrecoverableConsume kind) $ do
    _ <- anySingle
    pos <- unPos . sourceLine <$> getSourcePos
    pure $ Token kind "" pos

peek :: Parser Token
peek = lookAhead anySingle

tryPeek :: Parser (Maybe Token)
tryPeek = MP.optional (lookAhead anySingle)

tryPeekOrEOF :: Parser Token
tryPeekOrEOF = fromMaybe (Token TokenEOF "tryPeekOrEOF" 0) <$> MP.optional (lookAhead anySingle)

anySingle :: Parser Token
anySingle = satisfy (const True)

confirm :: TokenKind -> Parser ()
confirm kind = void $ lookAhead (consume kind)

parseCommaSeparatedUntil :: TokenKind -> Parser a -> Parser [a]
parseCommaSeparatedUntil = parseSequence TokenComma

parseExhaustiveSequence :: TokenKind -> Parser a -> Parser [a]
parseExhaustiveSequence separator itemParser = do
    first <- itemParser
    rest <- MP.many $ do
        nextTok <- tryPeekOrEOF
        if tokenKind nextTok == separator
            then do
                _ <- consume separator
                itemParser
            else MP.empty
    pure (first : rest)

parseSequence :: TokenKind -> TokenKind -> Parser a -> Parser [a]
parseSequence separator end itemParser = do
    inc <- tryPeekOrEOF
    if tokenKind inc == end
        then pure []
        else do
            first <- itemParser
            rest <- MP.many $ do
                nextTok <- tryPeekOrEOF
                case tokenKind nextTok of
                    k | k == separator -> do
                        _ <- consume separator
                        itemParser
                    k | k == end -> MP.empty
                    _ -> MP.customFailure $ ExpectedDifferentToken separator nextTok
            pure (first : rest)

parseFluidSequence :: TokenKind -> Parser a -> Parser [a]
parseFluidSequence end itemParser = do
    inc <- tryPeekOrEOF
    if tokenKind inc == end
        then pure []
        else do
            first <- itemParser
            rest <- MP.many $ do
                nextTok <- tryPeekOrEOF
                case tokenKind nextTok of
                    k | k == end -> MP.empty
                    _ -> itemParser
            pure (first : rest)

parseInLayout :: Parser a -> Parser a
parseInLayout = between (consume TokenLayoutStart) (consume TokenLayoutEnd)

parseLayout :: Parser a -> Parser [a]
parseLayout itemParser = do
    _ <- consume TokenLayoutStart
    items <- parseSequence TokenLayoutSeparator TokenLayoutEnd itemWithRecovery
    _ <- consume TokenLayoutEnd
    pure items
  where
    itemWithRecovery = withRecovery itemParser $ do
        skipUntilSync [TokenLayoutSeparator, TokenLayoutEnd]
        MP.customFailure $ ExpectedAnExpression (Token TokenLayoutSeparator "" 0)

parseOptionallyLayout :: Parser a -> Parser [a]
parseOptionallyLayout p = do
    inc <- tryPeek
    case inc of
        Just Token{tokenKind = TokenLayoutStart} -> parseLayout p
        _ -> pure []

parseOptionallyInLayout :: Parser a -> Parser a
parseOptionallyInLayout p = do
    inc <- tryPeek
    case inc of
        Just Token{tokenKind = TokenLayoutStart} -> do
            consume TokenLayoutStart >> p <* consume TokenLayoutEnd
        _ -> p

parseWithErrors :: Parser a -> [Token] -> Either (NonEmpty (ParseError TokenStream ParsingError)) (a, [ParseError TokenStream ParsingError])
parseWithErrors parser tokens =
    case parseWithRecovery parser tokens of
        Left errs -> Left (NE.fromList errs)
        Right (result, errs) -> Right (result, errs)

parseStrict :: Parser a -> [Token] -> Either (ParseErrorBundle TokenStream ParsingError) a
parseStrict parser tokens =
    runParser (evalStateT parser initialParserState) "" (TokenStream tokens)

runParserTokens :: Parser a -> [Token] -> Either (ParseErrorBundle TokenStream ParsingError) (a, [Token])
runParserTokens parser tokens =
    runParser action "" (TokenStream tokens)
  where
    action = do
        (val, _ps) <- runStateT parser initialParserState
        pstate <- MP.getParserState
        let remaining = case MP.stateInput pstate of
                TokenStream ts -> ts
        pure (val, remaining)

extractFromParseError :: ParseError TokenStream ParsingError -> [ParsingError]
extractFromParseError pe =
    case pe of
        TrivialError{} -> []
        FancyError _ fancySet ->
            [e | ErrorCustom e <- Set.toList fancySet]

extractFromBundle :: ParseErrorBundle TokenStream ParsingError -> [ParsingError]
extractFromBundle bundle =
    concatMap extractFromParseError (NE.toList $ bundleErrors bundle)

dropParsedTokens ::
    Parser a ->
    [Token] ->
    [Token]
dropParsedTokens parser tokens =
    case runParserTokens parser tokens of
        Right (_, leftover) -> leftover
        Left _bundle -> []

parseFuncName :: Parser String
parseFuncName = withRecovery parseFuncName'
    $ do
        pure "@ERROR"
  where
    parseFuncName' = do
        inc <- peek
        case tokenKind inc of
            TokenLowerIdentifier ->
                tokenValue <$> consume TokenLowerIdentifier
            TokenLeftBraces -> do
                _ <- consume TokenLeftBraces
                nameToken <- consume TokenVarSymbol
                _ <- consume TokenRightBraces
                pure $ tokenValue nameToken
            _ -> MP.customFailure $ InvalidFunctionName inc
