module Main where

import Config.Options (Options (optionsInput), extractOptions, formatError)
import Control.Monad (unless)
import qualified Data.Map as Map
import Inference.Resolver (runResolver)
import Inference.Tree (analyzeTreeT)
import Lexing.Lexer (tokenizeFile)
import Logging.ErrorPrinter (printConclusionMessage, printError)
import Logging.PrettyTrees (TreeShow (treeShow))
import Parsing.Ast (parse)
import Syntax.Tree (Expr, exprChildren)
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
    unless (Prelude.null errors) $ do
        mapM_ (\err -> printError err "app.soma" content "LEXING") errors
        printConclusionMessage ("Could not compile because of the " ++ show (length errors) ++ " lexing errors above.")
        exitFailure

    tree <-
        either
            ( \err -> do
                printError err "app.soma" content "PARSING"
                exitFailure
            )
            return
            (parse tokens)

    resolvedTreeIO <- runResolver tree
    (resolvedTree, finalEnv) <-
        either
            ( \err -> do
                printError err "app.soma" content "ANALYSIS"
                exitFailure
            )
            return
            resolvedTreeIO
    putStrLn $ "Env: " ++ show finalEnv

    putStrLn "Tree:"
    prettyPrintAst resolvedTree

    typeMap <-
        either
            ( \errors -> do
                mapM_ (\err -> printError err "app.soma" content "INFERENCE") errors
                exitFailure
            )
            return
            (analyzeTreeT finalEnv resolvedTree)
    putStrLn $ "Type map: " ++ treeShow typeMap
    putStrLn "Successfully compiled!"

prettyPrintAst :: Expr -> IO ()
prettyPrintAst root = prettyPrintAst' root 0
  where
    prettyPrintAst' expr indent = do
        putStrLn $ replicate indent ' ' ++ treeShow expr
        mapM_ (\child -> prettyPrintAst' child (indent + 2)) (exprChildren expr)
