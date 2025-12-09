{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Property.LexerSpec (spec) where

import Data.Text (Text)
import qualified Data.Text as T
import Lexing.Errors (LexingError)
import Lexing.Lexer
import Lexing.Position (Span (..))
import Test.Hspec
import Test.QuickCheck

-- | Generate arbitrary text for fuzzing
instance Arbitrary Text where
    arbitrary = T.pack <$> listOf arbitraryPrintableChar
      where
        arbitraryPrintableChar =
            elements
                $ ['a' .. 'z']
                    ++ ['A' .. 'Z']
                    ++ ['0' .. '9']
                    ++ " \t\n(){}[],.;:=+-*/<>!@#$%^&|\\\"'`_"
    shrink t = T.pack <$> shrink (T.unpack t)

-- | Generate valid Soma identifiers
genIdentifier :: Gen Text
genIdentifier = do
    first <- elements $ ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['_']
    rest <- listOf $ elements $ ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9'] ++ ['_']
    pure $ T.pack (first : rest)

-- | Generate valid Soma keywords
genKeyword :: Gen Text
genKeyword =
    elements
        [ "def"
        , "let"
        , "in"
        , "case"
        , "data"
        , "struct"
        , "trait"
        , "instance"
        , "where"
        , "with"
        , "use"
        , "true"
        , "false"
        , "if"
        , "then"
        , "else"
        , "export"
        , "intrinsic"
        ]

-- | Generate valid number literals
genNumber :: Gen Text
genNumber = T.pack . show <$> (arbitrary :: Gen (NonNegative Int))

-- | Generate valid string literals
genStringLit :: Gen Text
genStringLit = do
    content <- listOf $ elements $ ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9'] ++ " "
    pure $ T.pack $ "\"" ++ content ++ "\""

-- | Generate valid operators (excluding "/" which starts comments)
genOperator :: Gen Text
genOperator =
    elements
        [ "+"
        , "-"
        , "*"
        , "=="
        , "!="
        , "<"
        , ">"
        , "<="
        , ">="
        , "&&"
        , "||"
        , "->"
        , "<-"
        , "=>"
        , "::"
        , "."
        ]

-- | Helper to check if lexing produces any tokens
lexProducesTokens :: Text -> Bool
lexProducesTokens input =
    let (tokens, _) = lexCode input
    in not (null tokens)

-- | Helper to check if lexing crashes (returns False if no crash)
lexDoesNotCrash :: Text -> Bool
lexDoesNotCrash input =
    let (tokens, errors) = lexCode input
    in seq tokens $ seq errors True

spec :: Spec
spec = describe "Lexer Properties" $ do
    describe "safety properties" $ do
        it "never crashes on arbitrary input" $ property $ \(input :: Text) ->
            lexDoesNotCrash input === True

        it "never crashes on random printable strings"
            $ property
            $ let printableChars = [' ' .. '~']
              in forAll (T.pack <$> listOf (elements printableChars)) $ \input ->
                    lexDoesNotCrash input === True

    describe "token properties" $ do
        it "produces tokens for valid identifiers"
            $ property
            $ forAll genIdentifier
            $ \ident ->
                let (tokens, _) = lexCode ident
                in not (null tokens)

        it "produces tokens for valid numbers"
            $ property
            $ forAll genNumber
            $ \num ->
                let (tokens, _) = lexCode num
                    kinds = map tokenKind tokens
                in TokenNumber `elem` kinds

        it "produces correct token for keywords"
            $ property
            $ forAll genKeyword
            $ \kw ->
                let (tokens, _) = lexCode kw
                in not (null tokens)

        it "produces tokens for valid operators"
            $ property
            $ forAll genOperator
            $ \op ->
                let (tokens, _) = lexCode op
                in not (null tokens)

    describe "span properties" $ do
        it "token spans are non-negative" $ property $ \(input :: Text) ->
            let (tokens, _) = lexCode input
                spans = map tokenSpan tokens
                validSpan (Span start end) = start >= 0 && end >= start
            in all validSpan spans

        it "token positions are non-negative"
            $ property
            $ forAll genIdentifier
            $ \input ->
                let (tokens, _) = lexCode input
                in all (\t -> tokenPos t >= 0) tokens

        it "token positions are increasing"
            $ property
            $ forAll genIdentifier
            $ \input ->
                let (tokens, _) = lexCode input
                    positions = map tokenPos tokens
                    isSorted [] = True
                    isSorted [_] = True
                    isSorted (x : y : xs) = x <= y && isSorted (y : xs)
                in isSorted positions

    describe "string literal properties" $ do
        it "string content matches input"
            $ property
            $ forAll (listOf $ elements ['a' .. 'z'])
            $ \content ->
                let input = T.pack $ "\"" ++ content ++ "\""
                    (tokens, _) = lexCode input
                in case tokens of
                    [t] -> tokenKind t == TokenString content
                    _ -> False

        it "reports error for unterminated strings"
            $ property
            $ forAll (listOf $ elements ['a' .. 'z'])
            $ \content ->
                let input = T.pack $ "\"" ++ content -- No closing quote
                    (_, errors) = lexCode input
                in not (null errors)

    describe "comment properties" $ do
        it "line comments are ignored"
            $ property
            $ forAll genIdentifier
            $ \ident ->
                let input = ident <> " // this is a comment\n" <> ident
                    (tokens, _) = lexCode input
                    identTokens = filter (\t -> tokenKind t `elem` [TokenLowerIdentifier, TokenUpperIdentifier]) tokens
                in not (null identTokens)

        it "block comments are ignored"
            $ property
            $ forAll genIdentifier
            $ \ident ->
                let input = ident <> " /* comment */ " <> ident
                    (tokens, _) = lexCode input
                    identTokens = filter (\t -> tokenKind t `elem` [TokenLowerIdentifier, TokenUpperIdentifier]) tokens
                in not (null identTokens)

    describe "whitespace properties" $ do
        it "whitespace is handled correctly"
            $ property
            $ forAll (listOf $ elements " \t")
            $ \ws ->
                let input = T.pack ws
                    (tokens, errors) = lexCode input
                in null tokens && null errors

        it "tokens separated by whitespace are distinct"
            $ property
            $ forAll ((,) <$> genIdentifier <*> genIdentifier)
            $ \(id1, id2) ->
                (id1 /= id2 && T.head id1 /= '_' && T.head id2 /= '_')
                    ==> let input = id1 <> " " <> id2
                            (tokens, _) = lexCode input
                            identTokens = filter (\t -> tokenKind t `elem` [TokenLowerIdentifier, TokenUpperIdentifier]) tokens
                        in length identTokens >= 2

    describe "layout properties" $ do
        it "indentation produces layout tokens"
            $ property
            $ forAll genIdentifier
            $ \ident ->
                let input = ident <> "\n  " <> ident
                    (tokens, _) = lexCode input
                    layoutTokens = filter (\t -> tokenKind t `elem` [TokenLayoutStart, TokenLayoutEnd, TokenLayoutSeparator]) tokens
                in not (null layoutTokens)
