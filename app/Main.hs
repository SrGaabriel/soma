module Main where

import Lexing.Lexer (tokenizeFile)
import Parsing.Parser (parse)

main :: IO ()
main = do
    putStrLn "Starting soma..."
    content <- readFile "app.soma"

    let tokens = tokenizeFile "app.soma" content

    let tree = parse tokens

    putStrLn content
    putStrLn "Tokens:"
    print tokens
    putStrLn "Tree:"
    print tree