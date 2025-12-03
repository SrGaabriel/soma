{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Parsing.Parser (
    Parser,
    TokenStream (..),
    ParserContext (..),
    consumeRelevant,
    initialErrorState,
    recordError,
    getErrors,
    getContext,
    pushContext,
    popContext,
    withinContext,
    getOffset,
    withRecovery,
    satisfy,
    anySingle,
    consume,
    consumeAnyOf,
    peek,
    tryPeek,
    tryPeekOrEOF,
    tryPeekOrPlaceholderEOF,
    confirm,
    isEOF,
    skipUntilSync,
    recoverStatement,
    parseCommaSeparatedUntil,
    parseExhaustiveSequence,
    parseSequence,
    parseFluidSequence,
    parseInLayout,
    parseLayout,
    parseOptionallyLayout,
    parseOptionallyInLayout,
    parseFuncName,
    manyWithProgress,
    optionallySurround,
) where

import Control.Monad (void, when)
import Control.Monad.State.Strict (StateT, gets, modify)
import Data.Functor (($>))
import qualified Data.List.NonEmpty as NE
import qualified Data.Set as Set
import Lexing.Lexer (Token (..), TokenKind (..), tokenKind)
import Parsing.Errors (ParsingError (..))
import Text.Megaparsec hiding (Token, anySingle, satisfy, token, withRecovery)
import qualified Text.Megaparsec as MP
import Utils.Lists (hardTail)

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
        let tokens' = unTokenStream (pstateInput pstate)
            (pre, post) = splitAt (offset - pstateOffset pstate) tokens'
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

data ParserContext
    = TopLevel
    | InFunctionSignature String
    | InFunctionBody String
    | InPatternMatch String
    | InDataDeclaration String
    | InTraitDeclaration String
    | InInstanceDeclaration String
    | InTypeExpression
    deriving (Show, Eq)

data ErrorState = ErrorState
    { accumulatedErrors :: [ParseError TokenStream ParsingError]
    , currentContext :: [ParserContext]
    }

initialErrorState :: ErrorState
initialErrorState = ErrorState [] [TopLevel]

type Parser = StateT ErrorState (Parsec ParsingError TokenStream)

recordError :: ParseError TokenStream ParsingError -> Parser ()
recordError err = modify $ \s -> s{accumulatedErrors = err : accumulatedErrors s}

getErrors :: Parser [ParseError TokenStream ParsingError]
getErrors = gets (reverse . accumulatedErrors)

getContext :: Parser [ParserContext]
getContext = gets currentContext

pushContext :: ParserContext -> Parser ()
pushContext ctx = modify $ \s -> s{currentContext = ctx : currentContext s}

popContext :: Parser ()
popContext = modify $ \s -> s{currentContext = hardTail (currentContext s)}

withinContext :: ParserContext -> Parser a -> Parser a
withinContext ctx parser = do
    pushContext ctx
    result <- parser
    popContext
    pure result

withRecovery :: Parser a -> Parser a -> Parser a
withRecovery = (<|>)

satisfy :: (Token -> Bool) -> Parser Token
satisfy f = MP.token test Set.empty
  where
    test t
        | f t = Just t
        | otherwise = Nothing

anySingle :: Parser Token
anySingle = satisfy (const True)

consume :: TokenKind -> Parser Token
consume kind = do
    tok <- optional $ satisfy (\t -> tokenKind t == kind)
    case tok of
        Just t -> pure t
        Nothing -> do
            actual <- tryPeekOrEOF
            customFailure
                $ ExpectedDifferentToken
                    { expectedTok = kind
                    , receivedTok = actual
                    }

consumeRelevant :: TokenKind -> Parser Token
consumeRelevant kind = do
    tok <- optional $ satisfy (\t -> tokenKind t == kind || tokenKind t == TokenLayoutSeparator)
    case tok of
        Just t -> case tokenKind t of
            TokenLayoutSeparator -> consumeRelevant kind
            _ -> pure t
        Nothing -> do
            actual <- tryPeekOrEOF
            customFailure
                $ ExpectedDifferentToken
                    { expectedTok = kind
                    , receivedTok = actual
                    }

consumeAnyOf :: [TokenKind] -> Parser Token
consumeAnyOf kinds = do
    tok <- optional $ satisfy (\t -> tokenKind t `elem` kinds)
    case tok of
        Just t -> pure t
        Nothing -> do
            actual <- tryPeekOrEOF
            customFailure
                $ ExpectedOneOfTokens
                    { expectedTokens = kinds
                    , receivedToken = actual
                    }

peek :: Parser Token
peek = lookAhead anySingle

tryPeek :: Parser (Maybe Token)
tryPeek = optional (lookAhead anySingle)

tryPeekOrEOF :: Parser Token
tryPeekOrEOF = do
    mtok <- optional (lookAhead anySingle)
    case mtok of
        Just tok -> pure tok
        Nothing -> pure $ Token TokenEOF "EOF" 0

tryPeekOrPlaceholderEOF :: Parser Token
tryPeekOrPlaceholderEOF = tryPeekOrEOF

confirm :: TokenKind -> Parser ()
confirm kind = void $ lookAhead (consume kind)

isEOF :: Parser Bool
isEOF = do
    mtok <- optional (lookAhead anySingle)
    case mtok of
        Nothing -> pure True
        Just Token{tokenKind = TokenEOF} -> pure True
        _ -> pure False

skipUntilSync :: [TokenKind] -> Parser ()
skipUntilSync syncTokens = do
    void $ manyTill skipOne (lookAhead syncPoint <|> eof)
  where
    syncPoint = choice [void (satisfy (\t -> tokenKind t `elem` syncTokens))]
    skipOne = do
        tok <- anySingle
        when (tokenKind tok == TokenLayoutStart)
            $ void
            $ manyTill anySingle (satisfy (\t -> tokenKind t == TokenLayoutEnd))

recoverStatement :: Parser a -> a -> Parser a
recoverStatement parser defaultValue =
    parser <|> (skipUntilSync syncTokens $> defaultValue)
  where
    syncTokens =
        [ TokenLayoutSeparator
        , TokenLayoutEnd
        , TokenLet
        , TokenData
        , TokenDef
        ]

parseCommaSeparatedUntil :: TokenKind -> Parser a -> Parser [a]
parseCommaSeparatedUntil = parseSequence TokenComma

parseExhaustiveSequence :: TokenKind -> Parser a -> Parser [a]
parseExhaustiveSequence separator itemParser = do
    first <- itemParser
    rest <- many $ do
        nextTok <- tryPeekOrEOF
        if tokenKind nextTok == separator
            then do
                _ <- consume separator
                itemParser
            else empty
    pure (first : rest)

parseSequence :: TokenKind -> TokenKind -> Parser a -> Parser [a]
parseSequence separator end itemParser = do
    inc <- tryPeekOrEOF
    if tokenKind inc == end
        then pure []
        else do
            first <- itemParser
            rest <- many $ do
                nextTok <- tryPeekOrEOF
                case tokenKind nextTok of
                    k | k == separator -> do
                        _ <- consume separator
                        itemParser
                    k | k == end -> empty
                    _ -> customFailure $ ExpectedDifferentToken separator nextTok
            pure (first : rest)

parseFluidSequence :: TokenKind -> Parser a -> Parser [a]
parseFluidSequence end itemParser = do
    inc <- tryPeekOrEOF
    if tokenKind inc == end
        then pure []
        else do
            first <- itemParser
            rest <- many $ do
                nextTok <- tryPeekOrEOF
                case tokenKind nextTok of
                    k | k == end -> empty
                    _ -> itemParser
            pure (first : rest)

parseInLayout :: Parser a -> Parser a
parseInLayout = between (consume TokenLayoutStart) (consume TokenLayoutEnd)

parseLayout :: Parser a -> Parser [a]
parseLayout itemParser = do
    _ <- consume TokenLayoutStart
    items <- parseLayoutItems itemParser
    _ <- consume TokenLayoutEnd
    pure items
  where
    parseLayoutItems :: Parser a -> Parser [a]
    parseLayoutItems p = do
        inc <- tryPeekOrEOF
        if tokenKind inc == TokenLayoutEnd
            then pure []
            else do
                mItem <- parseItemWithRecovery p
                nextTok <- tryPeekOrEOF
                when (tokenKind nextTok == TokenLayoutSeparator)
                    $ void
                    $ consume TokenLayoutSeparator
                rest <- parseLayoutItems p
                pure $ case mItem of
                    Just item -> item : rest
                    Nothing -> rest

    parseItemWithRecovery :: Parser a -> Parser (Maybe a)
    parseItemWithRecovery p = do
        result <- observing p
        case result of
            Right val -> pure (Just val)
            Left err -> do
                ctx <- getContext
                when (isCoherentError ctx err) $ recordError err

                let syncTokens = case ctx of
                        (InPatternMatch _ : _) -> [TokenPipe, TokenLayoutSeparator, TokenLayoutEnd]
                        _ -> [TokenLayoutSeparator, TokenLayoutEnd]
                skipUntilSync syncTokens
                pure Nothing

    isCoherentError :: [ParserContext] -> ParseError TokenStream ParsingError -> Bool
    isCoherentError ctx err = case getCustomErrors err of
        (customErr : _) -> case customErr of
            ExpectedDifferentToken expected received
                | expected `elem` [TokenDef, TokenData, TokenTrait, TokenIntrinsic]
                , any isInsideDefinition ctx ->
                    False
                | expected == TokenDef
                , isExpressionToken received ->
                    False
            ExpectedAnExpression tok
                | tokenKind tok /= TokenEOF -> False
            _ -> True
        [] -> True
      where
        isInsideDefinition (InFunctionBody _) = True
        isInsideDefinition (InPatternMatch _) = True
        isInsideDefinition (InFunctionSignature _) = True
        isInsideDefinition _ = False

        isExpressionToken tok = case tokenKind tok of
            TokenTrue -> True
            TokenFalse -> True
            TokenLowerIdentifier -> True
            TokenUpperIdentifier -> True
            TokenNumber -> True
            TokenString _ -> True
            TokenLambda -> True
            TokenLet -> True
            TokenIf -> True
            TokenCase -> True
            TokenCompose -> True
            TokenBind -> True
            TokenLeftParen -> True
            TokenLeftBracket -> True
            _ -> False

        getCustomErrors (FancyError _ errSet) = [e | ErrorCustom e <- Set.toList errSet]
        getCustomErrors _ = []

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

parseFuncName :: Parser String
parseFuncName = parseFuncName' <|> pure "@ERROR"
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
            _ -> customFailure $ InvalidFunctionName inc

manyWithProgress :: Parser a -> Parser [a]
manyWithProgress p = do
    results <- go []
    pure (reverse results)
  where
    go acc = do
        startPos <- getOffset
        isAtEnd <- isEOF
        if isAtEnd
            then pure acc
            else do
                result <- optional p
                case result of
                    Nothing -> pure acc
                    Just x -> do
                        endPos <- getOffset
                        if endPos <= startPos
                            then do
                                _ <- anySingle
                                pure acc
                            else go (x : acc)

optionallySurround :: TokenKind -> TokenKind -> Parser a -> Parser a
optionallySurround openKind closeKind p = do
    inc <- tryPeekOrEOF
    if tokenKind inc == openKind
        then do
            consume openKind >> p <* consume closeKind
        else p
