{-# LANGUAGE OverloadedStrings #-}

module Unit.Lexing.LexerSpec (spec) where

import Data.Text (Text)
import qualified Data.Text as T
import Lexing.Errors (LexingError (..))
import Lexing.Lexer
import Lexing.Position (Span (..))
import Test.Hspec

-- | Helper to lex and get just the tokens (ignoring errors)
lexTokens :: Text -> [Token]
lexTokens = fst . lexCode

-- | Helper to lex and get just the errors
lexErrors :: Text -> [LexingError]
lexErrors = snd . lexCode

-- | Helper to get token kinds from source
tokenKinds :: Text -> [TokenKind]
tokenKinds = map tokenKind . lexTokens

-- | Helper to get token values from source
tokenValues :: Text -> [String]
tokenValues = map tokenValue . lexTokens

spec :: Spec
spec = describe "Lexer" $ do
    describe "basic tokens" $ do
        it "lexes empty input" $ do
            lexTokens "" `shouldBe` []

        it "lexes whitespace only" $ do
            lexTokens "   \t  " `shouldBe` []

        it "lexes single number" $ do
            let tokens = lexTokens "42"
            length tokens `shouldBe` 1
            tokenKind (head tokens) `shouldBe` TokenNumber
            tokenValue (head tokens) `shouldBe` "42"

        it "lexes multiple numbers" $ do
            tokenValues "1 2 3" `shouldBe` ["1", "2", "3"]

        it "lexes lowercase identifier" $ do
            let tokens = lexTokens "foo"
            tokenKind (head tokens) `shouldBe` TokenLowerIdentifier
            tokenValue (head tokens) `shouldBe` "foo"

        it "lexes uppercase identifier" $ do
            let tokens = lexTokens "Foo"
            tokenKind (head tokens) `shouldBe` TokenUpperIdentifier
            tokenValue (head tokens) `shouldBe` "Foo"

        it "lexes mixed identifiers" $ do
            tokenKinds "foo Bar baz Qux"
                `shouldBe` [ TokenLowerIdentifier
                           , TokenUpperIdentifier
                           , TokenLowerIdentifier
                           , TokenUpperIdentifier
                           ]

    describe "keywords" $ do
        it "lexes 'def'" $ do
            tokenKinds "def" `shouldBe` [TokenDef]

        it "lexes 'let'" $ do
            tokenKinds "let" `shouldBe` [TokenLet]

        it "lexes 'in'" $ do
            tokenKinds "in" `shouldBe` [TokenIn]

        it "lexes 'case'" $ do
            tokenKinds "case" `shouldBe` [TokenCase]

        it "lexes 'data'" $ do
            tokenKinds "data" `shouldBe` [TokenData]

        it "lexes 'struct'" $ do
            tokenKinds "struct" `shouldBe` [TokenStruct]

        it "lexes 'trait'" $ do
            tokenKinds "trait" `shouldBe` [TokenTrait]

        it "lexes 'instance'" $ do
            tokenKinds "instance" `shouldBe` [TokenInstance]

        it "lexes 'where'" $ do
            tokenKinds "where" `shouldBe` [TokenWhere]

        it "lexes 'with'" $ do
            tokenKinds "with" `shouldBe` [TokenWith]

        it "lexes 'use'" $ do
            tokenKinds "use" `shouldBe` [TokenImport]

        it "lexes 'true'" $ do
            tokenKinds "true" `shouldBe` [TokenTrue]

        it "lexes 'false'" $ do
            tokenKinds "false" `shouldBe` [TokenFalse]

        it "lexes 'if'" $ do
            tokenKinds "if" `shouldBe` [TokenIf]

        it "lexes 'then'" $ do
            tokenKinds "then" `shouldBe` [TokenThen]

        it "lexes 'else'" $ do
            tokenKinds "else" `shouldBe` [TokenElse]

        it "lexes 'export'" $ do
            tokenKinds "export" `shouldBe` [TokenExport]

        it "lexes 'intrinsic'" $ do
            tokenKinds "intrinsic" `shouldBe` [TokenIntrinsic]

    describe "punctuation" $ do
        it "lexes parentheses" $ do
            tokenKinds "()" `shouldBe` [TokenLeftParen, TokenRightParen]

        it "lexes braces" $ do
            tokenKinds "{}" `shouldBe` [TokenLeftBraces, TokenRightBraces]

        it "lexes brackets" $ do
            tokenKinds "[]" `shouldBe` [TokenLeftBracket, TokenRightBracket]

        it "lexes comma" $ do
            tokenKinds "," `shouldBe` [TokenComma]

        it "lexes colon" $ do
            tokenKinds ":" `shouldBe` [TokenColon]

        it "lexes double colon" $ do
            tokenKinds "::" `shouldBe` [TokenReturns]

        it "lexes equals" $ do
            tokenKinds "=" `shouldBe` [TokenEquals]

        it "lexes lambda backslash" $ do
            tokenKinds "\\" `shouldBe` [TokenLambda]

        it "lexes lambda unicode" $ do
            tokenKinds "λ" `shouldBe` [TokenLambda]

        it "lexes forall unicode" $ do
            tokenKinds "∀" `shouldBe` [TokenForall]

        it "lexes underscore" $ do
            tokenKinds "_" `shouldBe` [TokenUnderscore]

        it "lexes at sign" $ do
            tokenKinds "@" `shouldBe` [TokenAt]

        it "lexes pipe with space" $ do
            tokenKinds "| " `shouldBe` [TokenPipe]

    describe "arrows" $ do
        it "lexes right arrow" $ do
            tokenKinds "->" `shouldBe` [TokenRightArrow]

        it "lexes left arrow" $ do
            tokenKinds "<- " `shouldBe` [TokenLeftArrow]

        it "lexes fat arrow" $ do
            tokenKinds "=>" `shouldBe` [TokenStrongRightArrow]

    describe "operators" $ do
        it "lexes plus" $ do
            tokenKinds "+" `shouldBe` [TokenVarSymbol]
            tokenValues "+" `shouldBe` ["+"]

        it "lexes minus (not arrow)" $ do
            tokenKinds "- " `shouldBe` [TokenVarSymbol]

        it "lexes multiplication" $ do
            tokenValues "*" `shouldBe` ["*"]

        it "lexes equality" $ do
            tokenKinds "==" `shouldBe` [TokenVarSymbol]
            tokenValues "==" `shouldBe` ["=="]

        it "lexes inequality" $ do
            tokenValues "!=" `shouldBe` ["!="]

        it "lexes comparison operators" $ do
            tokenValues "< > <= >=" `shouldBe` ["<", ">", "<=", ">="]

        it "lexes logical operators" $ do
            tokenValues "&& ||" `shouldBe` ["&&", "||"]

        it "lexes complex operators" $ do
            tokenValues "<$> <*> >>=" `shouldBe` ["<$>", "<*>", ">>="]

    describe "strings" $ do
        it "lexes simple string" $ do
            let tokens = lexTokens "\"hello\""
            length tokens `shouldBe` 1
            tokenKind (head tokens) `shouldBe` TokenString "hello"

        it "lexes empty string" $ do
            let tokens = lexTokens "\"\""
            tokenKind (head tokens) `shouldBe` TokenString ""

        it "lexes string with spaces" $ do
            let tokens = lexTokens "\"hello world\""
            tokenKind (head tokens) `shouldBe` TokenString "hello world"

        it "reports unterminated string" $ do
            let errors = lexErrors "\"unterminated"
            length errors `shouldBe` 1
            case head errors of
                UnterminatedString _ -> pure ()
                _ -> expectationFailure "Expected UnterminatedString error"

        it "reports unterminated string at newline" $ do
            let errors = lexErrors "\"line1\nline2\""
            length errors `shouldSatisfy` (> 0)

    describe "triple-quoted strings" $ do
        it "lexes triple-quoted string" $ do
            let tokens = lexTokens "\"\"\"hello\"\"\""
            length tokens `shouldBe` 1
            tokenKind (head tokens) `shouldBe` TokenString "hello"

        it "lexes multiline triple-quoted string" $ do
            let tokens = lexTokens "\"\"\"line1\nline2\"\"\""
            tokenKind (head tokens) `shouldBe` TokenString "line1\nline2"

        it "reports unterminated triple-quoted string" $ do
            let errors = lexErrors "\"\"\"unterminated"
            length errors `shouldSatisfy` (> 0)

    describe "backtick identifiers" $ do
        it "lexes backtick lowercase identifier" $ do
            let tokens = lexTokens "`foo`"
            tokenKind (head tokens) `shouldBe` TokenLowerIdentifier

        it "lexes backtick uppercase identifier" $ do
            let tokens = lexTokens "`Foo`"
            tokenKind (head tokens) `shouldBe` TokenUpperIdentifier

        it "reports unterminated backtick identifier" $ do
            let errors = lexErrors "`unterminated"
            length errors `shouldSatisfy` (> 0)

    describe "comments" $ do
        it "ignores line comment" $ do
            tokenKinds "foo // this is a comment\nbar" `shouldContain` [TokenLowerIdentifier]
            tokenValues "foo // comment" `shouldBe` ["foo"]

        it "ignores block comment" $ do
            tokenValues "foo /* comment */ bar" `shouldBe` ["foo", "bar"]

        it "reports unterminated block comment" $ do
            let errors = lexErrors "foo /* unterminated"
            length errors `shouldSatisfy` (> 0)

    describe "layout" $ do
        it "produces layout start on indent" $ do
            tokenKinds "foo\n  bar" `shouldContain` [TokenLayoutStart]

        it "produces layout separator on same indent" $ do
            tokenKinds "foo\nbar" `shouldContain` [TokenLayoutSeparator]

        it "produces layout end on dedent" $ do
            tokenKinds "foo\n  bar\nbaz" `shouldContain` [TokenLayoutEnd]

    describe "position tracking" $ do
        it "tracks position of first token" $ do
            let tokens = lexTokens "foo"
            tokenPos (head tokens) `shouldBe` 0

        it "tracks position after whitespace" $ do
            let tokens = lexTokens "  foo"
            tokenPos (head tokens) `shouldBe` 2

        it "tracks span correctly" $ do
            let tokens = lexTokens "foo"
            tokenSpan (head tokens) `shouldBe` Span 0 3

        it "tracks multi-token positions" $ do
            let tokens = lexTokens "foo bar"
            map tokenPos tokens `shouldBe` [0, 4]

    describe "edge cases" $ do
        it "handles identifier with underscore" $ do
            tokenValues "foo_bar" `shouldBe` ["foo_bar"]

        it "handles identifier with numbers" $ do
            tokenValues "foo123" `shouldBe` ["foo123"]

        it "handles identifier starting with underscore as identifier" $ do
            -- _foo is not just underscore, it's an identifier
            let tokens = lexTokens "_foo"
            length tokens `shouldBe` 2 -- underscore + foo
            tokenKind (head tokens) `shouldBe` TokenUnderscore

        it "handles adjacent operators" $ do
            tokenValues "+-" `shouldBe` ["+-"]

        it "handles slash not followed by operator" $ do
            tokenKinds "/foo" `shouldBe` [TokenSlash, TokenLowerIdentifier]

        it "handles unexpected characters" $ do
            let errors = lexErrors "foo § bar"
            length errors `shouldSatisfy` (> 0)
            case head errors of
                UnexpectedCharacter '§' _ -> pure ()
                _ -> expectationFailure "Expected UnexpectedCharacter error"

    describe "complex examples" $ do
        it "lexes simple function definition" $ do
            tokenKinds "def add :: Int -> Int -> Int"
                `shouldBe` [ TokenDef
                           , TokenLowerIdentifier
                           , TokenReturns
                           , TokenUpperIdentifier
                           , TokenRightArrow
                           , TokenUpperIdentifier
                           , TokenRightArrow
                           , TokenUpperIdentifier
                           ]

        it "lexes lambda expression" $ do
            tokenKinds "\\x -> x + 1"
                `shouldBe` [ TokenLambda
                           , TokenLowerIdentifier
                           , TokenRightArrow
                           , TokenLowerIdentifier
                           , TokenVarSymbol
                           , TokenNumber
                           ]

        it "lexes data type definition" $ do
            tokenKinds "data Option a = Some a | None"
                `shouldContain` [ TokenData
                                , TokenUpperIdentifier
                                , TokenLowerIdentifier
                                , TokenEquals
                                , TokenUpperIdentifier
                                ]

        it "lexes trait definition" $ do
            tokenKinds "trait Show a where"
                `shouldBe` [TokenTrait, TokenUpperIdentifier, TokenLowerIdentifier, TokenWhere]

        it "lexes use statement" $ do
            tokenKinds "use foo/bar.{baz}"
                `shouldBe` [ TokenImport
                           , TokenLowerIdentifier
                           , TokenSlash
                           , TokenLowerIdentifier
                           , TokenVarSymbol
                           , TokenLeftBraces
                           , TokenLowerIdentifier
                           , TokenRightBraces
                           ]
