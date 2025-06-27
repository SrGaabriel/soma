module Main where

import Config.Options (Options (optionsInput), extractOptions, formatError)
import Control.Monad (unless)
import qualified Data.Map as Map
import Inference.Resolver (runResolverWithEnv)
import Inference.Tree (analyzeTreeT)
import Lexing.Lexer (tokenizeFile)
import Logging.ErrorPrinter (printConclusionMessage, printError)
import Logging.PrettyTrees (TreeShow (treeShow))
import Parsing.Ast (parse)
import Syntax.Tree (Expr, exprChildren)
import System.Exit (exitFailure)
import qualified Data.Set as Set
import Project.Module
import Project.Graph
import Project.Processing

main :: IO ()
main = do
    putStrLn "Starting soma..."
    optionsResult <- extractOptions
    options <- case optionsResult of
        Right opts -> return opts
        Left err -> do
            putStrLn $ "Error parsing command line arguments: " ++ formatError err
            exitFailure

    let rootDir = optionsInput options

    discoveredModules <- findModules rootDir
    putStrLn $ "Discovered modules: " ++ show (map fst discoveredModules)

    moduleGraph <- buildModuleGraph discoveredModules

    let depGraph = buildDependencyGraph moduleGraph

    case topoSortModules depGraph of
        Left cycles -> do
            putStrLn "Error: Detected cyclic imports between modules:"
            mapM_ (putStrLn . ("  " ++) . show) cycles
            exitFailure
        Right sortedModules -> do
            putStrLn $ "Processing modules in order: " ++ show sortedModules
            processModules sortedModules moduleGraph

    putStrLn "✅ Successfully compiled all modules."

prettyPrintAst :: Expr -> IO ()
prettyPrintAst root = prettyPrintAst' root 0
  where
    prettyPrintAst' expr indent = do
        putStrLn $ replicate indent ' ' ++ treeShow expr
        mapM_ (\child -> prettyPrintAst' child (indent + 2)) (exprChildren expr)
