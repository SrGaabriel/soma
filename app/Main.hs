module Main where

import Lexing.Lexer (tokenizeFile)

main :: IO ()
main = do
    putStrLn "Starting soma..."
    content <- readFile "app.soma"
    let tokens = tokenizeFile "app.soma" content
    putStrLn content
    print tokens