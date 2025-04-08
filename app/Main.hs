module Main where

import Analysis.Inference (TypeMap)
import Analysis.Tree (runAnalysis)
import Config.Options (Options (optionsInput), extractOptions, formatError)
import Data.Map as Map
import Lexing.Lexer (tokenizeFile)
import Logging.ErrorPrinter (printConclusionMessage, printError)
import Parsing.Parser (parse)
import Parsing.Tree (Expression (..), exprChildren)
import System.Exit (exitFailure)

main :: IO ()
main = do
    putStrLn "Starting soma..."
    optionsResult <- extractOptions
    options <- case optionsResult of
        Right opts -> return opts
        Left err -> do
            putStrLn $ "Error parsing command line arguments: " ++ formatError err
            exitFailure

    content <- readFile (optionsInput options)
    let (tokens, errors) = tokenizeFile content
    if not (Prelude.null errors)
        then do
            mapM_
                ( \err -> do
                    printError err "app.soma" content "LEXING"
                )
                errors
            printConclusionMessage ("Could not compile because of the " ++ show (length errors) ++ " lexing errors above.")
            exitFailure
        else pure ()

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
