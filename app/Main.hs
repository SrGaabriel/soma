module Main where

import Analysis.Tree (inferExpr)
import Parsing.Parser (parse)
import Lexing.Lexer (tokenizeFile)
import Parsing.Tree (Expression(..), getChildren)
import Logging.ErrorPrinter (printError)
import System.Exit (exitFailure)
import Analysis.Inference (cleanRunInferM)

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

    tree <- either
        (\err -> do
             printError err "app.soma" content "PARSING"
             exitFailure
        )
        return (parse tokens)

    putStrLn "Tree:"
    prettyPrintAst tree

    (_, inference) <- cleanRunInferM (inferExpr tree) >>= \(result, finalState) ->
                either
                  (\err -> printError err "app.soma" content "INFERENCE" >> exitFailure)
                  (\res -> return (res, finalState))
                  result


    putStrLn "Inference"
    print inference
    

prettyPrintAst :: Expression -> IO ()
prettyPrintAst root = prettyPrintAst' root 0
  where
    prettyPrintAst' expr indent = do
      putStrLn $ replicate indent ' ' ++ show expr
      mapM_ (\child -> prettyPrintAst' child (indent + 2)) (getChildren $ exprKind expr)