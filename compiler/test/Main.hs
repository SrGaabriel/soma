module Main (main) where

import qualified Lexer
import qualified Parser
import Test.Hspec (hspec)

main :: IO ()
main = hspec $ do
    Lexer.spec
    Parser.spec
