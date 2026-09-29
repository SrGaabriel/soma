module Main (main) where

import qualified Lexer
import Test.Hspec (hspec)

main :: IO ()
main = hspec Lexer.spec
