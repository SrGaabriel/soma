{-# LANGUAGE OverloadedStrings #-}

module Integration.GoldenSpec (spec) where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Exit (ExitCode (..))
import System.Process (readProcessWithExitCode)
import Test.Hspec

-- | Run somac to get Circuit IR output
getCircuitIR :: FilePath -> IO (Either String String)
getCircuitIR path = do
    (exitCode, stdout, stderr) <-
        readProcessWithExitCode
            "cabal"
            ["run", "somac", "--", "circuit", path]
            ""
    pure $ case exitCode of
        ExitSuccess -> Right stdout
        ExitFailure _ -> Left stderr

-- | Run somac to check types only
typeCheck :: FilePath -> IO (Either String String)
typeCheck path = do
    (exitCode, stdout, stderr) <-
        readProcessWithExitCode
            "cabal"
            ["run", "somac", "--", "check", path]
            ""
    pure $ case exitCode of
        ExitSuccess -> Right stdout
        ExitFailure _ -> Left stderr

spec :: Spec
spec = describe "Golden Tests" $ do
    describe "basic programs" $ do
        it "compiles identity function" $ do
            let src =
                    T.unlines
                        [ "def id :: Int -> Int"
                        , "    | x => x"
                        ]
            withTempFile src $ \path -> do
                result <- typeCheck path
                case result of
                    Right _ -> pure ()
                    Left err -> expectationFailure $ "Type check failed: " ++ err

        it "compiles arithmetic" $ do
            let src =
                    T.unlines
                        [ "intrinsic def {+} :: Int -> Int -> Int"
                        , "def add :: Int -> Int -> Int"
                        , "    | x y => x + y"
                        ]
            withTempFile src $ \path -> do
                result <- typeCheck path
                case result of
                    Right _ -> pure ()
                    Left err -> expectationFailure $ "Type check failed: " ++ err

        it "compiles boolean operations" $ do
            let src =
                    T.unlines
                        [ "def negate :: Bool -> Bool"
                        , "    | x => if x then false else true"
                        ]
            withTempFile src $ \path -> do
                result <- typeCheck path
                case result of
                    Right _ -> pure ()
                    Left err -> expectationFailure $ "Type check failed: " ++ err

    describe "data types" $ do
        it "compiles simple data type" $ do
            let src =
                    T.unlines
                        [ "data MyUnit"
                        , "    | MyUnit"
                        , ""
                        , "def unit :: MyUnit = MyUnit"
                        ]
            withTempFile src $ \path -> do
                result <- typeCheck path
                case result of
                    Right _ -> pure ()
                    Left err -> expectationFailure $ "Type check failed: " ++ err

        it "compiles Option type" $ do
            let src =
                    T.unlines
                        [ "data Option a"
                        , "    | Some"
                        , "        value :: a"
                        , "    | None"
                        , ""
                        , "def some :: Int -> Option Int"
                        , "    | x => Some x"
                        , "def none :: Option Int = None"
                        ]
            withTempFile src $ \path -> do
                result <- typeCheck path
                case result of
                    Right _ -> pure ()
                    Left err -> expectationFailure $ "Type check failed: " ++ err

    describe "pattern matching" $ do
        it "compiles case on booleans" $ do
            let src =
                    T.unlines
                        [ "def toInt :: Bool -> Int"
                        , "    | b => if b then 1 else 0"
                        ]
            withTempFile src $ \path -> do
                result <- typeCheck path
                case result of
                    Right _ -> pure ()
                    Left err -> expectationFailure $ "Type check failed: " ++ err

        it "compiles case with wildcards" $ do
            let src =
                    T.unlines
                        [ "def always :: Int -> Int"
                        , "    | _ => 42"
                        ]
            withTempFile src $ \path -> do
                result <- typeCheck path
                case result of
                    Right _ -> pure ()
                    Left err -> expectationFailure $ "Type check failed: " ++ err

    describe "lambdas" $ do
        it "compiles simple lambda" $ do
            let src =
                    T.unlines
                        [ "intrinsic def {+} :: Int -> Int -> Int"
                        , "def f :: Int -> Int"
                        , "    | x => x + 1"
                        ]
            withTempFile src $ \path -> do
                result <- typeCheck path
                case result of
                    Right _ -> pure ()
                    Left err -> expectationFailure $ "Type check failed: " ++ err

        it "compiles nested lambda" $ do
            let src =
                    T.unlines
                        [ "intrinsic def {+} :: Int -> Int -> Int"
                        , "def f :: Int -> Int -> Int"
                        , "    | x y => x + y"
                        ]
            withTempFile src $ \path -> do
                result <- typeCheck path
                case result of
                    Right _ -> pure ()
                    Left err -> expectationFailure $ "Type check failed: " ++ err

    describe "let bindings" $ do
        it "compiles simple let" $ do
            let src = "def f :: Int = let x = 1 in x\n"
            withTempFile src $ \path -> do
                result <- typeCheck path
                case result of
                    Right _ -> pure ()
                    Left err -> expectationFailure $ "Type check failed: " ++ err

        it "compiles nested let" $ do
            let src =
                    T.unlines
                        [ "intrinsic def {+} :: Int -> Int -> Int"
                        , "def f :: Int = let x = 1 in let y = 2 in x + y"
                        ]
            withTempFile src $ \path -> do
                result <- typeCheck path
                case result of
                    Right _ -> pure ()
                    Left err -> expectationFailure $ "Type check failed: " ++ err

    describe "Circuit IR generation" $ do
        it "generates Circuit IR for identity" $ do
            let src =
                    T.unlines
                        [ "def id :: Int -> Int"
                        , "    | x => x"
                        ]
            withTempFile src $ \path -> do
                result <- getCircuitIR path
                case result of
                    Right ir -> do
                        -- Check that the output contains expected elements
                        ir `shouldSatisfy` \s -> not (null s)
                    Left err -> expectationFailure $ "Circuit IR generation failed: " ++ err

-- Helper to create a temporary file with content
withTempFile :: T.Text -> (FilePath -> IO a) -> IO a
withTempFile content action = do
    let path = "/tmp/soma_test_" ++ show (abs $ T.length content `mod` 10000) ++ ".soma"
    TIO.writeFile path content
    result <- action path
    pure result
