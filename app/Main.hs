module Main where

import Analysis.Inference (TypeMap)
import Analysis.Tree (runAnalysis)
import Data.Map as Map
import Lexing.Lexer (tokenizeFile)
import Logging.ErrorPrinter (printError)
import Parsing.Parser (parse)
import Parsing.Tree (Expression (..), exprChildren)
import System.Exit (exitFailure)

main :: IO ()
main = do
    putStrLn "Starting soma..."
    content <- readFile "app.soma"

    tokens <-
        either
            ( \err -> do
                printError err "app.soma" content "LEXING"
                exitFailure
            )
            return
            (tokenizeFile content)

    tree <-
        either
            ( \err -> do
                printError err "app.soma" content "PARSING"
                exitFailure
            )
            return
            (parse tokens)

    putStrLn "Tree:"
    prettyPrintAst tree

    inferenceResult <- runAnalysis tree
    case inferenceResult of
        Left err -> do
            printError err "app.soma" content "ANALYSIS"
            exitFailure
        Right inference -> do
            prettyPrintTypeState inference

prettyPrintAst :: Expression -> IO ()
prettyPrintAst root = prettyPrintAst' root 0
  where
    prettyPrintAst' expr indent = do
        putStrLn $ replicate indent ' ' ++ show expr
        mapM_ (\child -> prettyPrintAst' child (indent + 2)) (exprChildren $ exprKind expr)

prettyPrintTypeState :: TypeMap -> IO ()
prettyPrintTypeState typeMap = do
    putStrLn "Type state:"
    mapM_ (\(expr, t) -> putStrLn $ show expr ++ " : " ++ show t) (Map.toList $ typeMap)
    putStrLn "End of type state"
