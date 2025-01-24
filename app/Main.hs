module Main where

import Lexing.Lexer (tokenizeFile)

main :: IO ()
main = do
    putStrLn "Starting soma..."
    content <- readAppFile
    let tokens = tokenizeFile "app.soma" content
    putStrLn content
    print tokens

readAppFile :: IO String
readAppFile = do
    content <- readFile "app.soma"
    return content