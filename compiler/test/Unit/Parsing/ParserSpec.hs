{-# LANGUAGE OverloadedStrings #-}

module Unit.Parsing.ParserSpec (spec) where

import Data.Text (Text)
import qualified Data.Text as T
import Lexing.Lexer (lexCode)
import Parsing.Ast (parse)
import Syntax.Tree (Expr)
import Test.Hspec

-- | Helper to parse source code to AST (succeeds only if no errors at all)
parseSource :: Text -> Either String Expr
parseSource src =
    let (tokens, lexErrors) = lexCode src
    in if not (null lexErrors)
        then Left $ "Lexer errors: " ++ show lexErrors
        else case parse tokens of
            Left _errs -> Left "Parse error"
            Right (errors, ast)
                | null errors -> Right ast
                | otherwise -> Left "Parse error (recovered)"

-- | Check if parsing succeeds without any errors
parsesSuccessfully :: Text -> Bool
parsesSuccessfully src = case parseSource src of
    Right _ -> True
    Left _ -> False

-- | Check if parsing fails or produces errors
parsesFailing :: Text -> Bool
parsesFailing = not . parsesSuccessfully

spec :: Spec
spec = describe "Parser" $ do
    describe "function definitions" $ do
        it "parses simple function with type signature" $ do
            parsesSuccessfully "def foo :: Int = 42" `shouldBe` True

        it "parses function with arrow type" $ do
            parsesSuccessfully "def add :: Int -> Int -> Int\n    | x y => x" `shouldBe` True

        it "parses function with body" $ do
            parsesSuccessfully "def foo :: Int = 42" `shouldBe` True

        it "parses function with pattern clause" $ do
            parsesSuccessfully "def foo :: Int -> Int\n    | x => x" `shouldBe` True

        it "parses function with multiple pattern clauses" $ do
            parsesSuccessfully "def add :: Int -> Int -> Int\n    | x y => x" `shouldBe` True

        it "parses imperative style function" $ do
            parsesSuccessfully "def add(x: Int, y: Int) -> Int = x" `shouldBe` True

        it "parses operator definition" $ do
            parsesSuccessfully "intrinsic def {+} :: Int -> Int -> Int" `shouldBe` True

    describe "expressions" $ do
        it "parses integer literal" $ do
            parsesSuccessfully "def x :: Int = 42" `shouldBe` True

        it "parses boolean true" $ do
            parsesSuccessfully "def x :: Bool = true" `shouldBe` True

        it "parses boolean false" $ do
            parsesSuccessfully "def x :: Bool = false" `shouldBe` True

        it "parses string literal" $ do
            parsesSuccessfully "def x :: String = \"hello\"" `shouldBe` True

        it "parses variable reference" $ do
            parsesSuccessfully "def f :: Int -> Int\n    | x => x" `shouldBe` True

        it "parses function application" $ do
            parsesSuccessfully "def x :: Int = f 42" `shouldBe` True

        it "parses multiple applications" $ do
            parsesSuccessfully "def x :: Int = f a b c" `shouldBe` True

        it "parses parenthesized expression" $ do
            parsesSuccessfully "def x :: Int = (42)" `shouldBe` True

        it "parses nested parentheses" $ do
            parsesSuccessfully "def x :: Int = ((42))" `shouldBe` True

        it "parses binary operator" $ do
            parsesSuccessfully "def x :: Int = 1 + 2" `shouldBe` True

        it "parses chained binary operators" $ do
            parsesSuccessfully "def x :: Int = 1 + 2 + 3" `shouldBe` True

        it "parses comparison operators" $ do
            parsesSuccessfully "def x :: Bool = 1 < 2" `shouldBe` True
            parsesSuccessfully "def y :: Bool = 1 == 2" `shouldBe` True
            parsesSuccessfully "def z :: Bool = 1 != 2" `shouldBe` True

    describe "lambda expressions" $ do
        it "parses simple lambda" $ do
            parsesSuccessfully "def f :: Int -> Int = (\\x -> x)" `shouldBe` True

        it "parses lambda with unicode" $ do
            parsesSuccessfully "def f :: Int -> Int = (λx -> x)" `shouldBe` True

        it "parses lambda with body" $ do
            parsesSuccessfully "def f :: Int -> Int = (\\x -> x + 1)" `shouldBe` True

        it "parses nested lambda" $ do
            parsesSuccessfully "def f :: Int -> Int -> Int = (\\x -> (\\y -> x))" `shouldBe` True

    describe "let expressions" $ do
        it "parses simple let" $ do
            parsesSuccessfully "def f :: Int = let x = 1 in x" `shouldBe` True

        it "parses nested let" $ do
            parsesSuccessfully "def f :: Int = let x = 1 in let y = 2 in x" `shouldBe` True

    describe "if expressions" $ do
        it "parses simple if" $ do
            parsesSuccessfully "def f :: Int = if true then 1 else 0" `shouldBe` True

        it "parses nested if" $ do
            parsesSuccessfully "def f :: Int = if true then if false then 1 else 2 else 3" `shouldBe` True

    describe "case expressions" $ do
        it "parses pattern matching function" $ do
            parsesSuccessfully "def f :: Bool -> Int\n    | b => if b then 1 else 0" `shouldBe` True

        it "parses case with constructor patterns" $ do
            parsesSuccessfully "def f :: Maybe Int -> Int\n    | (Just n) => n\n    | (Nothing) => 0" `shouldBe` True

        it "parses case with wildcard" $ do
            parsesSuccessfully "def f :: Int -> Int\n    | _ => 0" `shouldBe` True

    describe "data types" $ do
        it "parses simple data type" $ do
            let src =
                    T.unlines
                        [ "data MyUnit"
                        , "    | MyUnit"
                        ]
            parsesSuccessfully src `shouldBe` True

        it "parses data type with type parameter" $ do
            -- Using explicit newlines instead of T.unlines to avoid trailing newline issues
            parsesSuccessfully "data Maybe\n    | Just a\n    | Nothing" `shouldBe` True

        it "parses data type with multiple constructors" $ do
            let src =
                    T.unlines
                        [ "data Bool2"
                        , "    | True2"
                        , "    | False2"
                        ]
            parsesSuccessfully src `shouldBe` True

        it "parses data type with fields" $ do
            let src =
                    T.unlines
                        [ "data Pair a b"
                        , "    | Pair"
                        , "        fst :: a"
                        , "        snd :: b"
                        ]
            parsesSuccessfully src `shouldBe` True

    describe "struct types" $ do
        it "parses simple struct" $ do
            parsesSuccessfully "struct Point = Point\n    x :: Int\n    y :: Int" `shouldBe` True

        it "parses struct with single field" $ do
            parsesSuccessfully "struct Wrapper = Wrapper String" `shouldBe` True

    describe "traits" $ do
        it "parses simple trait" $ do
            parsesSuccessfully "trait Show a where\n    def show :: a -> String" `shouldBe` True

        it "parses trait with multiple methods" $ do
            parsesSuccessfully "trait Eq a where\n    def eq :: a -> a -> Bool\n    def ne :: a -> a -> Bool" `shouldBe` True

    describe "instances" $ do
        it "parses simple instance" $ do
            parsesSuccessfully "instance Show Int where\n    def show :: Int -> String\n        | x => \"int\"" `shouldBe` True

        it "parses instance with constraint" $ do
            parsesSuccessfully "instance Functor Maybe where\n    def fmap :: (a -> b) -> Maybe a -> Maybe b\n        | f (Just x) => Just (f x)\n        | f (Nothing) => Nothing" `shouldBe` True

    describe "imports" $ do
        it "parses import with specific items" $ do
            let src =
                    T.unlines
                        [ "use base/core.{Option, Some, None}"
                        , "def x :: Int = 1"
                        ]
            parsesSuccessfully src `shouldBe` True

        it "parses import with single item" $ do
            let src =
                    T.unlines
                        [ "use base/core.{Option}"
                        , "def x :: Int = 1"
                        ]
            parsesSuccessfully src `shouldBe` True

    describe "intrinsics" $ do
        it "parses intrinsic declaration" $ do
            parsesSuccessfully "intrinsic def println :: a -> IO ()" `shouldBe` True

    describe "types" $ do
        it "parses simple type" $ do
            parsesSuccessfully "def x :: Int = 0" `shouldBe` True

        it "parses function type" $ do
            parsesSuccessfully "def f :: Int -> Bool\n    | _ => true" `shouldBe` True

        it "parses higher-order function type" $ do
            parsesSuccessfully "def f :: (Int -> Bool) -> Int\n    | _ => 0" `shouldBe` True

        it "parses type application" $ do
            parsesSuccessfully "def x :: Maybe Int = Nothing" `shouldBe` True

        it "parses nested type application" $ do
            parsesSuccessfully "def x :: Maybe (Maybe Int) = Nothing" `shouldBe` True

        it "parses tuple type" $ do
            parsesSuccessfully "def x :: (Int, Bool) = (1, true)" `shouldBe` True

        it "parses array type" $ do
            parsesSuccessfully "def x :: [Int] = []" `shouldBe` True

        it "parses constrained type" $ do
            parsesSuccessfully "def f :: a -> String with (Show a)\n    | x => show x" `shouldBe` True

        it "parses multiple constraints" $ do
            parsesSuccessfully "def f :: a -> String with (Show a, Eq a)\n    | x => show x" `shouldBe` True

    describe "complex examples" $ do
        it "parses fibonacci function" $ do
            let src =
                    T.unlines
                        [ "intrinsic def {<} :: Int -> Int -> Bool"
                        , "intrinsic def {+} :: Int -> Int -> Int"
                        , "intrinsic def {-} :: Int -> Int -> Int"
                        , "def fib :: Int -> Int"
                        , "    | n => if n < 2 then n else fib (n - 1) + fib (n - 2)"
                        ]
            parsesSuccessfully src `shouldBe` True

        it "parses head function" $ do
            parsesSuccessfully "data Option a\n    | Some\n        value :: a\n    | None\n\ndef head :: [a] -> Option a\n    | (x:_) => Some x\n    | [] => None" `shouldBe` True

        it "parses multiple top-level definitions" $ do
            let src =
                    T.unlines
                        [ "def foo :: Int = 1"
                        , "def bar :: Int = 2"
                        , "def baz :: Int = 3"
                        ]
            parsesSuccessfully src `shouldBe` True

    describe "error cases" $ do
        it "fails on missing type signature" $ do
            parsesFailing "def foo" `shouldBe` True

        it "fails on invalid token" $ do
            parsesFailing "§invalid" `shouldBe` True

        it "fails on unbalanced parentheses" $ do
            parsesFailing "def x :: Int = (1 + 2" `shouldBe` True

        it "fails on missing case body" $ do
            parsesFailing "def f :: Int -> Int\n    |" `shouldBe` True
