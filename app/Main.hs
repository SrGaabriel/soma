module Main where

import Config.Options
import Control.Monad (unless)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Lexing.Lexer (tokenizeFile)
import Project.Graph
import Project.Incremental (extractSymbolImports, processModulesIncremental)
import Project.Module
import Project.Parsing
import System.Directory (doesDirectoryExist, doesFileExist)
import System.Exit (exitFailure, exitSuccess)
import System.FilePath (dropExtension, takeExtension, takeFileName)

main :: IO ()
main = do
    command <- extractCommand
    putStrLn "Soma Compiler v0.1.0"
    case command of
        Right (Build options) -> build options
        Right (Lex file) -> do
            content <- readFile file
            let (lexed, lexErrors) = tokenizeFile content
            case lexErrors of
                [] -> do
                    putStrLn $ "Lexing succeeded with " ++ show (length lexed) ++ " tokens:"
                    mapM_ print lexed
                    exitSuccess
                errs -> mapM_ print errs >> exitFailure
        Right (Parse file) -> do
            parseE <- parseModule (dropExtension (takeFileName file), file)
            case parseE of
                Right mi -> do
                    putStrLn $ "Parsing succeeded for module: " ++ moduleName mi
                    exitSuccess
                Left _ -> exitFailure
        Left err -> putStrLn (formatError err) >> exitFailure

build :: Options -> IO ()
build options = do
    putStrLn $ "Compiling with options: " ++ show options

    let inp = optionsInput options
    isFile <- doesFileExist inp
    if isFile && takeExtension inp == ".soma"
        then
            processSingle options
        else do
            isDir <- doesDirectoryExist inp
            unless isDir (putStrLn "Error: input is neither a .soma file nor a directory" >> exitFailure)

            let name = fromMaybe (error "Error: please pass --name to the compiler") (optionsName options)
            mods <- findModules name inp
            putStrLn $ "Discovered modules: " ++ show (map fst mods)

            graphE <- buildModuleGraph mods
            graph <- case graphE of
                Left _errs -> putStrLn "Failed to parse at least one module" >> exitFailure
                Right g -> return g

            let depGraph = buildDependencyGraph graph
            case topoSortModules depGraph of
                Left cycles -> do
                    putStrLn "Error: Detected cyclic imports between modules:"
                    mapM_ (putStrLn . ("  " ++) . show) cycles
                    exitFailure
                Right sorted -> do
                    _ <- processModulesIncremental sorted graph options
                    return ()

            putStrLn "Successfully compiled all modules."
            exitSuccess

processSingle :: Options -> IO ()
processSingle options = do
    let path = optionsInput options
    let name = dropExtension (takeFileName path)
    parseE <- parseModule (name, path)
    mi <- case parseE of
        Left _ -> exitFailure
        Right m -> return m

    let ast = moduleAst mi
        graph = Map.singleton (moduleName mi) mi
        depGraph = buildDependencyGraph graph
    let imports = extractSymbolImports ast

    unless (null imports) $ do
        putStrLn "Error: Standalone modules can't import other modules." >> exitFailure

    case topoSortModules depGraph of
        Left cycles -> do
            putStrLn "Error: Detected cyclic imports in module:"
            mapM_ (putStrLn . ("  " ++) . show) cycles
            exitFailure
        Right sorted -> do
            _ <- processModulesIncremental sorted graph options{optionsName = Just name}
            return ()

    putStrLn "Successfully compiled module."
    exitSuccess
