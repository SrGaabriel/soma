{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Parser (spec) where

import Control.Monad (forM, forM_)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Maple.Cache (mkCache)
import Maple.Green (GreenNode (GreenNode, gnWidth))
import Maple.Print (prettyGreen, showKind)
import Soma.Diagnostic (reportAll)
import Soma.File (SourceFile (SourceFile, srcContent, srcPath), readSource)
import Soma.Syntax.Kind (Kind)
import Soma.Syntax.Lexer (lexAll)
import Soma.Syntax.Parser (parseRoot, runParser)
import System.Directory (listDirectory)
import Test.Hspec (Spec, describe, it, runIO, shouldBe)

fixturesDir :: String
fixturesDir = "compiler/test/fixtures/parser/"

sources :: IO [SourceFile]
sources = do
    dir <- listDirectory fixturesDir
    forM dir $ \src -> readSource $ fixturesDir <> src

spec :: Spec
spec = describe "basic.soma" $ do
    files <- runIO sources
    forM_ files $ \src@SourceFile{srcPath, srcContent} -> do
        it (srcPath <> ": lexes without diagnostics") $ do
            let (toks, diag) = lexAll srcContent
            putStrLn $ show toks
            diag `shouldBe` []

        it (srcPath <> ":parses without diagnostics") $ do
            ((root, _), diag) <- runParser src mkCache parseRoot
            TIO.putStrLn $ prettyGreen (showKind @Kind) root
            reportAll diag
            diag `shouldBe` []

        it (srcPath <> ": parses with the same tree size as source length") $ do
            ((GreenNode{gnWidth}, _), _) <- runParser src mkCache parseRoot
            gnWidth `shouldBe` (T.length srcContent)
