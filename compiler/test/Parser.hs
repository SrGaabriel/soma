{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Parser (spec) where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Maple.Cache (mkCache)
import Maple.Green (GreenNode (GreenNode, gnWidth))
import Maple.Print (prettyGreen, showKind)
import Soma.File (SourceFile (SourceFile, srcContent, srcPath))
import Soma.Syntax.Kind (Kind)
import Soma.Syntax.Lexer (lexAll)
import Soma.Syntax.Parser (parseRoot, runParser)
import Test.Hspec (Spec, describe, it, shouldBe)
import Soma.Diagnostic (reportAll)

basicSource :: SourceFile
basicSource =
    SourceFile
        { srcPath = "test/basic.soma"
        , srcContent = "def id (a : Nat) : Nat := a"
        }

spec :: Spec
spec = describe "basic.soma" $ do
    it "lexes without diagnostics" $ do
        let (toks, diag) = lexAll . srcContent $ basicSource
        putStrLn $ show toks
        diag `shouldBe` []

    it "parses without diagnostics" $ do
        ((root, _), diag) <- runParser basicSource mkCache parseRoot
        TIO.putStrLn $ prettyGreen (showKind @Kind) root
        reportAll diag
        diag `shouldBe` []

    it "parses with the same tree size as source length" $ do
        ((GreenNode{gnWidth}, _), _) <- runParser basicSource mkCache parseRoot
        gnWidth `shouldBe` (T.length . srcContent $ basicSource)
