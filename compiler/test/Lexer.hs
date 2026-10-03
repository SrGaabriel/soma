{-# LANGUAGE OverloadedStrings #-}

module Lexer (spec) where

import Soma.Syntax.Kind
import Soma.Syntax.Lexer (Token (tKind), lexAll)
import Test.Hspec (Spec, describe, it, shouldBe)

spec :: Spec
spec = describe "Lexer" $ do
    it "lexes 2*2"
        $ do
            let (tokens, diag) = lexAll "2*2"
            diag `shouldBe` []
            (map tKind tokens) `shouldBe` [KNumber, KStar, KNumber, KEof]
