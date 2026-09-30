{-# LANGUAGE OverloadedStrings #-}

module Lexer (spec) where

import Data.Functor.Identity (Identity)
import qualified Data.Text as T
import Maple.Green (RawKind)
import Soma.Syntax.Kind
import Soma.Syntax.Lexer (LexerState (..), LexerT, runLexer)
import qualified Soma.Syntax.Lexer as Lexer
import Test.Hspec (Spec, describe, it, shouldBe)

lexAll :: T.Text -> [RawKind]
lexAll input = fst $ runLexer LexerState{lxText = input, lxCursor = 0} go
  where
    go :: LexerT Identity [RawKind]
    go = do
        kind <- Lexer.lex
        if kind == tEof
            then pure [kind]
            else (kind :) <$> go

spec :: Spec
spec = describe "Lexer" $ do
    it "lexes 2*2"
        $ lexAll "2*2" `shouldBe` [tNumber, tStar, tNumber, tEof]
