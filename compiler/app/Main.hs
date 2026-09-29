module Main (main) where

import Somac.Cli (runCli)

main :: IO ()
main = do
    cli <- runCli
    putStrLn $ show cli
    pure ()
