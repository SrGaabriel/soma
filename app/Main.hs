module Main where

import Parsing.Parser (parse)
import Lexing.Lexer (tokenizeFile)
import Parsing.Tree (Expression(..), getChildren)
import Logging.ErrorPrinter (printError)
import System.Exit (exitFailure)

main :: IO ()
main = do
    putStrLn "Starting soma..."
    content <- readFile "app.soma"

    tokens <- either 
      (\err -> do
         printError err "app.soma" content "LEXING" 
         exitFailure
      )
      return (tokenizeFile "app.soma" content)

    let tree = parse tokens
    case tree of
      Left err ->
        printError err "app.soma" content "PARSING"
      Right tree' -> do
        putStrLn "Tree:"
        prettyPrintAst tree'

prettyPrintAst :: Expression -> IO ()
prettyPrintAst root = prettyPrintAst' root 0
  where
    prettyPrintAst' expr indent = do
      putStrLn $ replicate indent ' ' ++ show expr
      mapM_ (\child -> prettyPrintAst' child (indent + 2)) (getChildren $ exprKind expr)