module Main where

import Config.Options (Options (optionsInput), extractOptions, formatError)
import Lexing.Lexer (tokenizeFile)
import Parsing.Ast (parse)
import Logging.ErrorPrinter (printConclusionMessage, printError)
import System.Exit (exitFailure)
import Syntax.Tree (Expr, exprChildren)

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

prettyPrintAst :: Expr -> IO ()
prettyPrintAst root = prettyPrintAst' root 0
  where
    prettyPrintAst' expr indent = do
        putStrLn $ replicate indent ' ' ++ show expr
        mapM_ (\child -> prettyPrintAst' child (indent + 2)) (exprChildren expr)