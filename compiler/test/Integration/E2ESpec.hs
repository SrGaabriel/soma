{-# LANGUAGE OverloadedStrings #-}

module Integration.E2ESpec (spec) where

import Control.Monad (when)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (doesFileExist, removeFile)
import System.Exit (ExitCode (..))
import System.Process (readProcessWithExitCode)
import Test.Hspec

-- | Compile and run a Soma program, returning the output
compileAndRun :: T.Text -> IO (Either String String)
compileAndRun source = do
    let srcPath = "/tmp/e2e_test.soma"
    let outPath = "/tmp/e2e_test"

    -- Write source
    TIO.writeFile srcPath source

    -- Compile
    (compileExit, _, compileErr) <-
        readProcessWithExitCode
            "cabal"
            ["run", "somac", "--", "build", srcPath, "--output", outPath]
            ""

    case compileExit of
        ExitFailure _ -> do
            cleanup srcPath outPath
            pure $ Left $ "Compilation failed: " ++ compileErr
        ExitSuccess -> do
            -- Check if output exists
            exists <- doesFileExist outPath
            if not exists
                then do
                    cleanup srcPath outPath
                    pure $ Left "Compiled binary not found"
                else do
                    -- Run
                    (runExit, runOut, runErr) <- readProcessWithExitCode outPath [] ""
                    cleanup srcPath outPath
                    case runExit of
                        ExitSuccess -> pure $ Right runOut
                        ExitFailure code ->
                            pure
                                $ Left
                                $ "Runtime error (exit " ++ show code ++ "): " ++ runErr

-- | Type-check only (faster for syntax/type tests)
typeCheckOnly :: T.Text -> IO (Either String ())
typeCheckOnly source = do
    let srcPath = "/tmp/typecheck_test.soma"
    TIO.writeFile srcPath source

    (exitCode, _, stderr) <-
        readProcessWithExitCode
            "cabal"
            ["run", "somac", "--", "check", srcPath]
            ""

    removeFileIfExists srcPath

    pure $ case exitCode of
        ExitSuccess -> Right ()
        ExitFailure _ -> Left stderr

cleanup :: FilePath -> FilePath -> IO ()
cleanup src out = do
    removeFileIfExists src
    removeFileIfExists out
    removeFileIfExists (out ++ ".ll")
    removeFileIfExists (out ++ ".o")

removeFileIfExists :: FilePath -> IO ()
removeFileIfExists path = do
    exists <- doesFileExist path
    when exists $ removeFile path

spec :: Spec
spec = describe "End-to-End Tests" $ do
    describe "type checking" $ do
        it "accepts well-typed programs" $ do
            result <- typeCheckOnly "def x :: Int = 42\n"
            result `shouldBe` Right ()

        it "rejects ill-typed programs" $ do
            result <- typeCheckOnly "def x :: Int = true\n"
            case result of
                Left _ -> pure () -- Expected to fail
                Right _ -> expectationFailure "Should have rejected ill-typed program"

        it "accepts polymorphic functions" $ do
            result <-
                typeCheckOnly
                    $ T.unlines
                        [ "def id :: a -> a"
                        , "    | x => x"
                        ]
            result `shouldBe` Right ()

        it "accepts higher-order functions" $ do
            result <-
                typeCheckOnly
                    $ T.unlines
                        [ "def apply :: (a -> b) -> a -> b"
                        , "    | f x => f x"
                        ]
            result `shouldBe` Right ()

    describe "basic expressions" $ do
        it "type checks integer literals" $ do
            result <- typeCheckOnly "def x :: Int = 42\n"
            result `shouldBe` Right ()

        it "type checks boolean literals" $ do
            result <-
                typeCheckOnly
                    $ T.unlines
                        [ "def x :: Bool = true"
                        , "def y :: Bool = false"
                        ]
            result `shouldBe` Right ()

        it "type checks string literals" $ do
            result <- typeCheckOnly "def x :: String = \"hello\"\n"
            result `shouldBe` Right ()

        it "type checks arithmetic" $ do
            result <-
                typeCheckOnly
                    $ T.unlines
                        [ "intrinsic def {+} :: Int -> Int -> Int"
                        , "intrinsic def {*} :: Int -> Int -> Int"
                        , "def x :: Int = 1 + 2 * 3"
                        ]
            result `shouldBe` Right ()

        it "type checks comparisons" $ do
            result <-
                typeCheckOnly
                    $ T.unlines
                        [ "intrinsic def {<} :: Int -> Int -> Bool"
                        , "intrinsic def {==} :: Int -> Int -> Bool"
                        , "def x :: Bool = 1 < 2"
                        , "def y :: Bool = 1 == 1"
                        ]
            result `shouldBe` Right ()

    describe "functions" $ do
        it "type checks unary function" $ do
            result <-
                typeCheckOnly
                    $ T.unlines
                        [ "intrinsic def {+} :: Int -> Int -> Int"
                        , "def succ :: Int -> Int"
                        , "    | x => x + 1"
                        ]
            result `shouldBe` Right ()

        it "type checks binary function" $ do
            result <-
                typeCheckOnly
                    $ T.unlines
                        [ "intrinsic def {+} :: Int -> Int -> Int"
                        , "def add :: Int -> Int -> Int"
                        , "    | x y => x + y"
                        ]
            result `shouldBe` Right ()

        it "type checks recursive function" $ do
            result <-
                typeCheckOnly
                    $ T.unlines
                        [ "intrinsic def {==} :: Int -> Int -> Bool"
                        , "intrinsic def {-} :: Int -> Int -> Int"
                        , "intrinsic def {*} :: Int -> Int -> Int"
                        , "def fac :: Int -> Int"
                        , "    | n => if n == 0 then 1 else n * fac (n - 1)"
                        ]
            result `shouldBe` Right ()

        it "type checks mutually recursive functions" $ do
            -- Mutual recursion may require forward declarations or special handling
            pending

    describe "data types" $ do
        it "type checks data type definition" $ do
            result <-
                typeCheckOnly
                    $ T.unlines
                        [ "data Bool2"
                        , "    | True2"
                        , "    | False2"
                        , ""
                        , "def x :: Bool2 = True2"
                        ]
            result `shouldBe` Right ()

        it "type checks parameterized data type" $ do
            result <-
                typeCheckOnly
                    $ T.unlines
                        [ "data Maybe a"
                        , "    | Just"
                        , "        value :: a"
                        , "    | Nothing"
                        , ""
                        , "def x :: Maybe Int = Just 42"
                        , "def y :: Maybe Int = Nothing"
                        ]
            result `shouldBe` Right ()

        it "type checks struct definition" $ do
            result <-
                typeCheckOnly
                    $ T.unlines
                        [ "struct Point = Point"
                        , "    x :: Int"
                        , "    y :: Int"
                        ]
            result `shouldBe` Right ()

    describe "pattern matching" $ do
        it "type checks case on custom type" $ do
            result <-
                typeCheckOnly
                    $ T.unlines
                        [ "data Maybe"
                        , "    | Just a"
                        , "    | Nothing"
                        , ""
                        , "def unwrap :: Maybe Int -> Int"
                        , "    | (Just n) => n"
                        , "    | (Nothing) => 0"
                        ]
            result `shouldBe` Right ()

        it "type checks nested patterns" $ do
            result <-
                typeCheckOnly
                    $ T.unlines
                        [ "data Maybe"
                        , "    | Just a"
                        , "    | Nothing"
                        , ""
                        , "def unwrap2 :: Maybe (Maybe Int) -> Int"
                        , "    | (Just (Just n)) => n"
                        , "    | _ => 0"
                        ]
            result `shouldBe` Right ()

    describe "traits and instances" $ do
        it "type checks trait definition" $ do
            result <-
                typeCheckOnly
                    $ T.unlines
                        [ "trait Show a where"
                        , "    def show :: a -> String"
                        ]
            result `shouldBe` Right ()

        it "type checks instance definition" $ do
            result <-
                typeCheckOnly
                    $ T.unlines
                        [ "trait Show a where"
                        , "    def show :: a -> String"
                        , ""
                        , "instance Show Int where"
                        , "    def show :: Int -> String"
                        , "        | x => \"int\""
                        ]
            result `shouldBe` Right ()

    describe "error cases" $ do
        it "rejects undefined variable" $ do
            result <- typeCheckOnly "def x :: Int = undefined_var\n"
            case result of
                Left _ -> pure ()
                Right _ -> expectationFailure "Should reject undefined variable"

        it "rejects type mismatch in function body" $ do
            result <- typeCheckOnly "def x :: Int = true\n"
            case result of
                Left _ -> pure ()
                Right _ -> expectationFailure "Should reject type mismatch"

        it "rejects type mismatch in function application" $ do
            result <-
                typeCheckOnly
                    $ T.unlines
                        [ "def f :: Int -> Int"
                        , "    | x => x"
                        , "def y :: Int = f true"
                        ]
            case result of
                Left _ -> pure ()
                Right _ -> expectationFailure "Should reject type mismatch in application"

        it "rejects non-exhaustive patterns" $ pending
    -- Pattern exhaustiveness checking may or may not be implemented

    describe "complex programs" $ do
        it "type checks fibonacci" $ do
            result <-
                typeCheckOnly
                    $ T.unlines
                        [ "intrinsic def {<} :: Int -> Int -> Bool"
                        , "intrinsic def {+} :: Int -> Int -> Int"
                        , "intrinsic def {-} :: Int -> Int -> Int"
                        , "def fib :: Int -> Int"
                        , "    | n => if n < 2 then n else fib (n - 1) + fib (n - 2)"
                        ]
            result `shouldBe` Right ()

        it "type checks list operations" $ do
            result <-
                typeCheckOnly
                    $ T.unlines
                        [ "data List a"
                        , "    | Cons"
                        , "        hd :: a"
                        , "        tl :: List a"
                        , "    | Nil"
                        , ""
                        , "def listHead :: List Int -> Int"
                        , "    | (Cons x _) => x"
                        , "    | (Nil) => 0"
                        ]
            result `shouldBe` Right ()
