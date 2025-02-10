module Main where

import Parsing.Parser (parse)
import Lexing.Lexer (tokenizeFile, Token (tokenPos, tokenValue))
import Parsing.Tree (Expression(..), getChildren)
import Parsing.Errors (getErrorToken, getErrorMessage)
import Logging.ErrorPrinter (printError)

main :: IO ()
main = do
    putStrLn "Starting soma..."
    content <- readFile "app.soma"

    let tokens = tokenizeFile "app.soma" content

    let tree = parse tokens
    case tree of
      Left err ->
        case getErrorToken err of
          Just token -> 
            let pos = tokenPos token in
            let end = pos + length (tokenValue token) - 1 in
            let message = getErrorMessage err in
              printError "app.soma" content "PARSING" pos end message
          Nothing -> print err
      Right tree' -> do
        putStrLn "Tree:"
        prettyPrintAst tree'

prettyPrintAst :: Expression -> IO ()
prettyPrintAst root = prettyPrintAst' root 0
  where
    prettyPrintAst' expr indent = do
      putStrLn $ replicate indent ' ' ++ show expr
      mapM_ (\child -> prettyPrintAst' child (indent + 2)) (getChildren $ exprKind expr)