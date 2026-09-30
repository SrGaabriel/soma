{-# LANGUAGE OverloadedStrings #-}

module Lexer (spec) where

import Soma.Syntax.Kind
import Soma.Syntax.Lexer (Token (tKind), lexAll)
import Test.Hspec (Spec, describe, it, shouldBe)

spec :: Spec
spec = describe "Lexer" $ do
    it "lexes 2*2"
        $ map (tKind) (lexAll "2*2") `shouldBe` [tNumber, tStar, tNumber, tEof]
