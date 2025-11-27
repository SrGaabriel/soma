module Main where

import Build.Incremental (processModulesIncremental)
import Config.Options
import Control.Monad (unless)
import qualified Data.ByteString as BS
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Text.Encoding as TE
import Lexing.Lexer (lexCode)
import Logging.Errors (printSomeError)
import Logging.Json (errorsToJsonOutput, failedJsonOutput, printJsonOutput)
import Project.Extracts (extractSymbolImports)
import Project.Graph
import Project.Module
import Project.Parsing
import System.Directory (doesDirectoryExist, doesFileExist)
import System.Exit (exitFailure, exitSuccess)
import System.FilePath (dropExtension, takeExtension, takeFileName)

main :: IO ()
main = do
    command <- extractCommand
    case command of
        Right (Check checkOpts) -> check checkOpts
        Right (Build options) -> do
            putStrLn "Soma Compiler v0.1.0"
            build options
        Right (Lex file) -> do
            putStrLn "Soma Compiler v0.1.0"
            fileContents <- BS.readFile file
            let content = TE.decodeUtf8 fileContents
            let (lexed, lexErrors) = lexCode content
            case lexErrors of
                [] -> do
                    putStrLn $ "Lexing succeeded with " ++ show (length lexed) ++ " tokens:"
                    mapM_ print lexed
                    exitSuccess
                errs -> mapM_ print errs >> exitFailure
        Right (Parse file) -> do
            putStrLn "Soma Compiler v0.1.0"
            parseE <- parseModule (dropExtension (takeFileName file)) file
            case parseE of
                Right mi -> do
                    putStrLn $ "Parsing succeeded for module: " ++ moduleName mi
                    exitSuccess
                Left errs -> do
                    mapM_ printSomeError errs
                    exitFailure
        Left err -> putStrLn (formatError err) >> exitFailure

check :: CheckOptions -> IO ()
check opts = do
    let path = checkInput opts

    isFile <- doesFileExist path
    if isFile && takeExtension path == ".soma"
        then checkSingleFile opts path
        else do
            isDir <- doesDirectoryExist path
            if isDir
                then checkDirectory opts path
                else do
                    case checkFormat opts of
                        FormatJson -> printJsonOutput (failedJsonOutput (checkName opts))
                        FormatHuman -> putStrLn "Error: input is neither a .soma file nor a directory"
                    exitFailure

checkSingleFile :: CheckOptions -> FilePath -> IO ()
checkSingleFile opts path = do
    let name = fromMaybe (dropExtension (takeFileName path)) (checkName opts)

    parseE <- parseModule name path
    case parseE of
        Left errs -> do
            case checkFormat opts of
                FormatJson -> do
                    let output = errorsToJsonOutput (Just name) errs
                    printJsonOutput output
                FormatHuman -> mapM_ printSomeError errs
            exitFailure
        Right _mi -> do
            case checkFormat opts of
                FormatJson -> do
                    let output = errorsToJsonOutput (Just name) []
                    printJsonOutput output
                FormatHuman -> putStrLn $ "Module " ++ name ++ " checked successfully."
            exitSuccess

checkDirectory :: CheckOptions -> FilePath -> IO ()
checkDirectory opts path = do
    let name = fromMaybe (error "Error: please pass --name when checking a directory") (checkName opts)

    mods <- findModules name path
    case checkFormat opts of
        FormatHuman -> putStrLn $ "Discovered modules: " ++ show (map fst mods)
        FormatJson -> return ()

    graphE <- buildModuleGraph mods
    case graphE of
        Left errs -> do
            case checkFormat opts of
                FormatJson -> do
                    let output = errorsToJsonOutput (Just name) errs
                    printJsonOutput output
                FormatHuman -> mapM_ printSomeError errs
            exitFailure
        Right _graph -> do
            case checkFormat opts of
                FormatJson -> do
                    let output = errorsToJsonOutput (Just name) []
                    printJsonOutput output
                FormatHuman -> putStrLn $ "All modules in " ++ name ++ " checked successfully."
            exitSuccess

build :: Options -> IO ()
build options = do
    putStrLn $ "Compiling with options: " ++ show options

    let inp = optionsInput options
    isFile <- doesFileExist inp
    if isFile && takeExtension inp == ".soma"
        then processSingle options
        else do
            isDir <- doesDirectoryExist inp
            unless isDir (putStrLn "Error: input is neither a .soma file nor a directory" >> exitFailure)

            let name = fromMaybe (error "Error: please pass --name to the compiler") (optionsName options)
            mods <- findModules name inp
            putStrLn $ "Discovered modules: " ++ show (map fst mods)

            graphE <- buildModuleGraph mods
            graph <- case graphE of
                Left errs -> do
                    mapM_ printSomeError errs
                    putStrLn "Failed to parse at least one module" >> exitFailure
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
    parseE <- parseModule name path
    mi <- case parseE of
        Left errs -> do
            mapM_ printSomeError errs
            putStrLn "Failed to parse module." >> exitFailure
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
