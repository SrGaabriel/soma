module Main where

import Config.Options (Options (optionsInput), extractOptions, formatError)
import Lexing.Lexer (tokenizeFile)
import Logging.ErrorPrinter (printConclusionMessage, printError)
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
    putStrLn $ "Lexing completed successfully: " ++ show tokens