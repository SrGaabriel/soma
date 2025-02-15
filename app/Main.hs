module Main where

import Data.Map as Map
import Analysis.Tree (inferExpr, runInference, TypeMap)
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

    inference <- either    
        (\err -> printError err "app.soma" content "INFERENCE" >> exitFailure)
        return (runInference tree)


    putStrLn "Inference"
    prettyPrintTypeState inference


prettyPrintAst :: Expression -> IO ()
prettyPrintAst root = prettyPrintAst' root 0
  where
    prettyPrintAst' expr indent = do
      putStrLn $ replicate indent ' ' ++ show expr
      mapM_ (\child -> prettyPrintAst' child (indent + 2)) (getChildren $ exprKind expr)

prettyPrintTypeState :: TypeMap -> IO ()
prettyPrintTypeState typeMap = do
  putStrLn "Type state:"
  mapM_ (\(expr, t) -> putStrLn $ show expr ++ " : " ++ show t) (Map.toList $ typeMap)
  putStrLn "End of type state"