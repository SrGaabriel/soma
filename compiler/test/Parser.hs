{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Parser (spec) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Maple.Cache (mkCache)
import Maple.Green (GreenNode (GreenNode, gnWidth))
import Soma.Syntax.Kind (Kind)
import Soma.Syntax.Lexer (lexAll)
import Soma.Syntax.Parser (parseRoot, runParser)
import Test.Hspec (Spec, describe, it, shouldBe)
import Maple.Print (prettyGreen, showKind)

basicSource :: Text
basicSource = "def id (a : Nat) : Nat := a"

spec :: Spec
spec = describe "basic.soma" $ do
    it "lexes without diagnostics" $ do
        let (toks, diag) = lexAll basicSource
        putStrLn $ show toks
        diag `shouldBe` []

    it "parses without diagnostics" $ do
        ((root, _), diag) <- runParser basicSource mkCache parseRoot
        TIO.putStrLn $ prettyGreen (showKind @Kind) root
        diag `shouldBe` []

    it "parses with the same tree size as source length" $ do
        ((GreenNode{gnWidth}, _), _) <- runParser basicSource mkCache parseRoot
        gnWidth `shouldBe` (T.length basicSource)
