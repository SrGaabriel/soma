{-# LANGUAGE OverloadedStrings #-}

-- | Shared test utilities for the Soma compiler test suite.
module Test.Utils (
    -- * Compilation helpers
    compileToCircuit,
    compileToAlloy,
    runSomac,
    runProgram,

    -- * File helpers
    withTempSomaFile,
    readFixture,
    readGolden,
    getProjectRoot,

    -- * Assertion helpers
    shouldContainError,
    shouldCompileSuccessfully,
    shouldFailWith,

    -- * Test data paths
    fixturesDir,
    goldenDir,
    regressionDir,
) where

import Control.Exception (bracket)
import Control.Monad (unless, when)
import Data.List (isInfixOf)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (doesFileExist, getCurrentDirectory, removeFile)
import System.Exit (ExitCode (..))
import System.FilePath (takeDirectory, (</>))
import System.IO (hClose, openTempFile)
import System.Process (readProcessWithExitCode)
import Test.Hspec

-- | Get the project root directory
getProjectRoot :: IO FilePath
getProjectRoot = do
    cwd <- getCurrentDirectory
    -- Navigate up from compiler/test to project root
    pure $ takeDirectory (takeDirectory cwd) </> ""

-- | Path to test fixtures
fixturesDir :: FilePath
fixturesDir = "compiler/test/fixtures"

-- | Path to golden test files
goldenDir :: FilePath
goldenDir = "compiler/test/golden"

-- | Path to regression test files
regressionDir :: FilePath
regressionDir = "compiler/test/regression"

-- | Read a fixture file
readFixture :: FilePath -> IO T.Text
readFixture name = TIO.readFile (fixturesDir </> name)

-- | Read a golden file
readGolden :: FilePath -> IO T.Text
readGolden name = TIO.readFile (goldenDir </> name)

-- | Run somac with given arguments
runSomac :: [String] -> IO (ExitCode, String, String)
runSomac args = readProcessWithExitCode "cabal" (["run", "somac", "--"] ++ args) ""

-- | Compile source to Circuit IR (as string)
compileToCircuit :: FilePath -> IO (Either String String)
compileToCircuit path = do
    (exitCode, stdout, stderr) <- runSomac ["circuit", "--input", path]
    pure $ case exitCode of
        ExitSuccess -> Right stdout
        ExitFailure _ -> Left stderr

-- | Compile source to Alloy IR (as string)
compileToAlloy :: FilePath -> IO (Either String String)
compileToAlloy path = do
    (exitCode, stdout, stderr) <- runSomac ["build", "--input", path]
    pure $ case exitCode of
        ExitSuccess -> Right stdout
        ExitFailure _ -> Left stderr

-- | Compile and run a program, returning stdout
runProgram :: T.Text -> IO (Either String String)
runProgram source = withTempSomaFile source $ \path -> do
    (exitCode, stdout, stderr) <- runSomac ["build", "--input", path, "--output", path ++ ".out"]
    case exitCode of
        ExitFailure _ -> pure $ Left stderr
        ExitSuccess -> do
            (runExit, runOut, runErr) <- readProcessWithExitCode (path ++ ".out") [] ""
            case runExit of
                ExitSuccess -> pure $ Right runOut
                ExitFailure _ -> pure $ Left runErr

-- | Create a temporary .soma file, run action, then clean up
withTempSomaFile :: T.Text -> (FilePath -> IO a) -> IO a
withTempSomaFile content action = bracket acquire release $ \(path, _) -> action path
  where
    acquire = do
        (path, h) <- openTempFile "/tmp" "test.soma"
        TIO.hPutStr h content
        hClose h
        pure (path, ())
    release (path, _) = do
        exists <- doesFileExist path
        when exists $ removeFile path
        let outPath = path ++ ".out"
        outExists <- doesFileExist outPath
        when outExists $ removeFile outPath

-- | Assert that output contains a specific error message
shouldContainError :: Either String a -> String -> Expectation
shouldContainError (Left err) expected =
    unless (expected `isInfixOf` err)
        $ expectationFailure
        $ "Expected error containing: " ++ expected ++ "\nBut got: " ++ err
shouldContainError (Right _) expected =
    expectationFailure $ "Expected error containing: " ++ expected ++ "\nBut compilation succeeded"

-- | Assert that compilation succeeds
shouldCompileSuccessfully :: Either String a -> Expectation
shouldCompileSuccessfully (Right _) = pure ()
shouldCompileSuccessfully (Left err) =
    expectationFailure $ "Expected successful compilation but got error: " ++ err

-- | Assert that compilation fails with a specific error
shouldFailWith :: Either String a -> String -> Expectation
shouldFailWith = shouldContainError
