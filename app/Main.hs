module Main where

import Data.Map as Map
import Analysis.Tree (inferExpr)
import Parsing.Parser (parse)
import Lexing.Lexer (tokenizeFile)
import Parsing.Tree (Expression(..), getChildren)
import Logging.ErrorPrinter (printError)
import System.Exit (exitFailure)
import Analysis.Inference (cleanRunInferM, InferState(..))

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
    prettyPrintTypeState inference
    

prettyPrintAst :: Expression -> IO ()
prettyPrintAst root = prettyPrintAst' root 0
  where
    prettyPrintAst' expr indent = do
      putStrLn $ replicate indent ' ' ++ show expr
      mapM_ (\child -> prettyPrintAst' child (indent + 2)) (getChildren $ exprKind expr)

prettyPrintTypeState :: InferState -> IO ()
prettyPrintTypeState state = do
  putStrLn "Type state:"
  mapM_ (\(expr, t) -> putStrLn $ show expr ++ " : " ++ show t) (Map.toList $ inferTypeMap state)
  putStrLn "End of type state"