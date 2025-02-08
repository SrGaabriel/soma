module Main where

import Parsing.Parser (parse)
import Lexing.Lexer (tokenizeFile)
import Parsing.Tree (Expression(..), getChildren)

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
    prettyPrintAst' expr indent = do
      putStrLn $ replicate indent ' ' ++ show expr
      mapM_ (\child -> prettyPrintAst' child (indent + 2)) (getChildren $ exprKind expr)