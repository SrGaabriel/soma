module Main where

import Parsing.Parser (parse)
import Parsing.Tree (Expression (Expression), getChildren)
import Lexing.Lexer (tokenizeFile, Token (tokenValue))

main :: IO ()
main = do
    putStrLn "Starting soma..."
    content <- readFile "app.soma"

    let tokens = tokenizeFile "app.soma" content

    let tree = parse tokens

    putStrLn content
    putStrLn "Tokens:"
    print tokens
    case tree of
      Left err -> print err
      Right tree' -> do
        putStrLn "Tree:"
        prettyPrintAst tree'

prettyPrintAst :: Expression -> IO ()
prettyPrintAst root = prettyPrintAst' root 0
  where
    prettyPrintAst' (Expression token kind) indent = do
      putStrLn $ replicate indent ' ' ++ (show kind) ++ " (value='" ++ tokenValue token ++ "')"
      mapM_ (\child -> prettyPrintAst' child (indent + 2)) (getChildren kind)