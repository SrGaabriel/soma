{-# LANGUAGE OverloadedStrings #-}

module Lexer (spec) where

import Control.Monad.State (evalStateT)
import Control.Monad.Writer (runWriterT)
import Data.Functor.Identity (Identity, runIdentity)
import qualified Data.Text as T
import Maple.Green (RawKind)
import Soma.Syntax.Kind
import Soma.Syntax.Lexer (LexerState (..), LexerT)
import qualified Soma.Syntax.Lexer as Lexer
import Test.Hspec (Spec, describe, it, shouldBe)

lexAll :: T.Text -> [RawKind]
lexAll input =
    fst . runIdentity . runWriterT
        $ evalStateT go LexerState{lxText = input, lxCursor = 0}
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
