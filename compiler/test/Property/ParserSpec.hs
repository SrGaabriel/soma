{-# LANGUAGE OverloadedStrings #-}

module Property.ParserSpec (spec) where

import Data.Text (Text)
import qualified Data.Text as T
import Lexing.Lexer (lexCode)
import Parsing.Ast (parse)
import Test.Hspec
import Test.QuickCheck

-- | Generate a simple valid expression
genSimpleExpr :: Gen Text
genSimpleExpr =
    oneof
        [ pure "42"
        , pure "true"
        , pure "false"
        , pure "x"
        , genParenExpr
        ]

genParenExpr :: Gen Text
genParenExpr = do
    inner <- genSimpleExpr
    pure $ "(" <> inner <> ")"

-- | Generate a valid function definition
genFunctionDef :: Gen Text
genFunctionDef = do
    name <- genLowerIdent
    ty <- genSimpleType
    body <- genSimpleExpr
    pure $ "def " <> name <> " :: " <> ty <> " = " <> body <> "\n"

-- | Generate a valid type
genSimpleType :: Gen Text
genSimpleType = elements ["Int", "Bool", "String", "Unit"]

-- | Generate a function type
genFunctionType :: Gen Text
genFunctionType = do
    arg <- genSimpleType
    ret <- genSimpleType
    pure $ arg <> " -> " <> ret

-- | Generate a lowercase identifier
genLowerIdent :: Gen Text
genLowerIdent = do
    first <- elements ['a' .. 'z']
    rest <- listOf $ elements $ ['a' .. 'z'] ++ ['0' .. '9'] ++ ['_']
    let ident = first : take 10 rest
    -- Avoid keywords
    if ident `elem` keywords
        then genLowerIdent
        else pure $ T.pack ident
  where
    keywords =
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
        , "bind"
        , "compose"
        ]

-- | Generate an uppercase identifier
genUpperIdent :: Gen Text
genUpperIdent = do
    first <- elements ['A' .. 'Z']
    rest <- listOf $ elements $ ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9']
    pure $ T.pack (first : take 10 rest)

-- | Helper to check if parsing succeeds without any errors
parsesOk :: Text -> Bool
parsesOk src =
    let (tokens, lexErrors) = lexCode src
    in null lexErrors && case parse tokens of
        Right (errors, _) -> null errors
        Left _ -> False

-- | Helper to check if parsing fails or produces errors
parsesFail :: Text -> Bool
parsesFail = not . parsesOk

-- | Helper to check parsing doesn't crash
parseDoesNotCrash :: Text -> Bool
parseDoesNotCrash src =
    let (tokens, _) = lexCode src
    in case parse tokens of
        Right _ -> True
        Left _ -> True

spec :: Spec
spec = describe "Parser Properties" $ do
    describe "safety properties" $ do
        it "never crashes on valid token streams"
            $ property
            $ forAll genFunctionDef
            $ \src ->
                parseDoesNotCrash src === True

        it "never crashes on random valid-ish input"
            $ property
            $ forAll (T.unlines <$> listOf genFunctionDef)
            $ \src ->
                parseDoesNotCrash src === True

    describe "acceptance properties" $ do
        it "accepts valid function definitions"
            $ property
            $ forAll genFunctionDef
            $ \src ->
                parsesOk src === True

        it "accepts multiple function definitions"
            $ property
            $ forAll (T.unlines <$> listOf1 genFunctionDef)
            $ \src ->
                parsesOk src === True

    describe "structural properties" $ do
        it "accepts parenthesized expressions"
            $ property
            $ forAll genSimpleExpr
            $ \expr ->
                let src = "def x :: Int = (" <> expr <> ")\n"
                in parsesOk src === True

        it "accepts nested parentheses"
            $ property
            $ forAll (choose (1, 5))
            $ \depth ->
                let parens = T.replicate depth "(" <> "42" <> T.replicate depth ")"
                    src = "def x :: Int = " <> parens <> "\n"
                in parsesOk src === True

    describe "type properties" $ do
        it "accepts simple types"
            $ property
            $ forAll genSimpleType
            $ \ty ->
                let src = "def x :: " <> ty <> " = 42\n"
                in parsesOk src === True

        it "accepts function types"
            $ property
            $ forAll genFunctionType
            $ \ty ->
                let src = "def f :: " <> ty <> "\n    | x => x\n"
                in parsesOk src === True

    describe "expression properties" $ do
        it "accepts integer literals"
            $ property
            $ forAll (arbitrary :: Gen (NonNegative Int))
            $ \(NonNegative n) ->
                let src = "def x :: Int = " <> T.pack (show n) <> "\n"
                in parsesOk src === True

        it "accepts binary operators"
            $ property
            $ forAll (elements ["+", "-", "*", "/", "==", "!=", "<", ">", "<=", ">="])
            $ \op ->
                let src = "def x :: Int = 1 " <> op <> " 2\n"
                in parsesOk src === True

        it "accepts chained binary operators"
            $ property
            $ forAll (elements ["+", "-", "*"])
            $ \op ->
                let src = "def x :: Int = 1 " <> op <> " 2 " <> op <> " 3\n"
                in parsesOk src === True

    describe "data type properties" $ do
        it "accepts simple data types"
            $ property
            $ forAll genUpperIdent
            $ \name ->
                let src = "data " <> name <> "\n    | " <> name <> "\n"
                in parsesOk src === True

        it "accepts data types with constructors"
            $ property
            $ forAll ((,) <$> genUpperIdent <*> genUpperIdent)
            $ \(name, con) ->
                name /= con
                    ==> let src = "data " <> name <> "\n    | " <> con <> "\n        value :: Int"
                        in parsesOk src === True

    describe "error properties" $ do
        it "rejects unbalanced parentheses"
            $ property
            $ forAll (choose (1, 5))
            $ \n ->
                let src = "def x :: Int = " <> T.replicate n "(" <> "42\n"
                in parsesFail src === True

        it "rejects missing type signature"
            $ parsesFail "def x = 42\n" `shouldBe` True

        it "rejects empty function body"
            $ parsesFail "def x :: Int =\n" `shouldBe` True
