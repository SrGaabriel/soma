module Main where

import Build.Incremental (extractIntrinsicNames, processExternalDependencies, processModulesIncremental)
import Circuit.Linearize (linearizeModule)
import Circuit.Lower (lowerModule)
import Circuit.Simplify (simplifyModule)
import Circuit.ToAlloy (lowerCircuitToAlloy)
import Config.Options
import Control.Monad (unless, when)
import qualified Data.ByteString as BS
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Text.Encoding as TE
import Format.Errors (CycleError (..), SomeError (..))
import Format.Trees (prettyPrintAst, treeShow)
import Lexing.Lexer (lexCode)
import Llvm.Gen.Entry (runLlvmCodeGenAndTranscribe)
import Logging.Errors (printError, printSomeError)
import Logging.Json (errorsToJsonOutput, failedJsonOutput, printJsonOutput)
import Logging.Trees (prettyCircuit, prettyCircuitGraph)
import Metal.Gen.Entry (compileMetalModule)
import Metal.Lift (liftLambdas)
import Metal.MonadNormalize (normalizeModule)
import Project.Check (CheckedModule (..), checkModule, checkModulesInOrder)
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
                    prettyPrintAst (moduleAst mi)
                    putStrLn $ "Parsing succeeded for module: " ++ moduleName mi
                    exitSuccess
                Left errs -> do
                    mapM_ printSomeError errs
                    exitFailure
        Right (Circuit circuitOpts) -> do
            putStrLn "Soma Compiler v0.1.0 - Circuit IR"
            circuit circuitOpts
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
        Right mi -> do
            (externalDeps, externalInstances, _, _) <- processExternalDependencies (checkDeps opts)
            let graph = Map.singleton name mi
                (errors, _) = checkModulesInOrder [name] graph externalDeps externalInstances name

            let allErrors =
                    concatMap
                        ( \(modName, errs) ->
                            map
                                ( \e -> case Map.lookup modName graph of
                                    Just modInfo -> SomeError e (modulePath modInfo) (moduleContent modInfo) "INFERENCE"
                                    Nothing -> SomeError e "" "" "INFERENCE"
                                )
                                errs
                        )
                        errors

            case checkFormat opts of
                FormatJson -> do
                    let output = errorsToJsonOutput (Just name) allErrors
                    printJsonOutput output
                FormatHuman ->
                    if null allErrors
                        then putStrLn $ "Module " ++ name ++ " checked successfully."
                        else mapM_ printSomeError allErrors

            if null allErrors
                then exitSuccess
                else exitFailure

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
        Right graph -> do
            let depGraph = buildDependencyGraph graph
            case topoSortModules depGraph of
                Left cycles -> do
                    case checkFormat opts of
                        FormatJson -> do
                            let cycleErrs = map (\c -> SomeError (CycleError c) "" "" "CHECK") cycles
                            let output = errorsToJsonOutput (Just name) cycleErrs
                            printJsonOutput output
                        FormatHuman -> do
                            putStrLn "Error: Detected cyclic imports between modules:"
                            mapM_ (putStrLn . ("  " ++) . show) cycles
                    exitFailure
                Right sorted -> do
                    (externalDeps, externalInstances, _, _) <- processExternalDependencies (checkDeps opts)

                    let (errors, _) = checkModulesInOrder sorted graph externalDeps externalInstances name

                    let allErrors =
                            concatMap
                                ( \(modName, errs) ->
                                    map
                                        ( \e -> case Map.lookup modName graph of
                                            Just mi -> SomeError e (modulePath mi) (moduleContent mi) "INFERENCE"
                                            Nothing -> SomeError e "" "" "INFERENCE"
                                        )
                                        errs
                                )
                                errors

                    case checkFormat opts of
                        FormatJson -> do
                            let output = errorsToJsonOutput (Just name) allErrors
                            printJsonOutput output
                        FormatHuman ->
                            if null allErrors
                                then putStrLn $ "All modules in " ++ name ++ " checked successfully."
                                else mapM_ printSomeError allErrors

                    if null allErrors
                        then exitSuccess
                        else exitFailure

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

-- | Lower a single file to Circuit IR and print the result
circuit :: CircuitOptions -> IO ()
circuit opts = do
    let path = circuitInput opts
        name = dropExtension (takeFileName path)

    parseE <- parseModule name path
    mi <- case parseE of
        Left errs -> do
            mapM_ printSomeError errs
            putStrLn "Failed to parse module." >> exitFailure
        Right m -> return m

    -- Type check the module
    let (allErrors, checked) = checkModule name mi Map.empty Map.empty Map.empty

    unless (null allErrors) $ do
        putStrLn $ "Errors while type checking module " ++ name ++ ":"
        mapM_ (\e -> printError e (modulePath mi) (moduleContent mi) "INFERENCE") allErrors
        exitFailure

    let resolvedAst = checkedResolvedAst checked
        types = checkedTypeMap checked

    -- Compile to Metal
    let metallic = compileMetalModule name resolvedAst types Map.empty
        intrinsics = extractIntrinsicNames resolvedAst
        metallicLifted = liftLambdas intrinsics metallic
        metallicNormalized = normalizeModule metallicLifted

    putStrLn "=== Metal HIR ==="
    putStrLn $ treeShow metallicNormalized
    putStrLn ""

    let circuitLowered = lowerModule metallicNormalized
        circuitModule = simplifyModule circuitLowered
        printer = if circuitGraphFormat opts then prettyCircuitGraph else prettyCircuit

    putStrLn "=== Circuit IR (before linearization) ==="
    putStrLn $ printer circuitModule

    -- Optionally linearize
    let finalModule =
            if circuitLinearize opts
                then linearizeModule circuitModule
                else circuitModule

    when (circuitLinearize opts) $ do
        putStrLn "=== Circuit IR (after linearization) ==="
        putStrLn $ printer finalModule

    -- Optionally lower to Alloy
    let showAlloy = circuitToAlloy opts || circuitToLlvm opts
    alloyModule <-
        if showAlloy
            then do
                -- For LLVM, we need linearization
                let linearizedModule =
                        if circuitLinearize opts
                            then finalModule
                            else linearizeModule circuitModule
                let alloy = lowerCircuitToAlloy linearizedModule
                when (circuitToAlloy opts) $ do
                    putStrLn "=== Alloy MIR ==="
                    putStrLn $ treeShow alloy
                pure (Just alloy)
            else pure Nothing

    -- Optionally lower to LLVM
    when (circuitToLlvm opts) $ case alloyModule of
        Just alloy -> do
            putStrLn "=== LLVM IR ==="
            let llvmIR = runLlvmCodeGenAndTranscribe alloy
            putStrLn llvmIR
        Nothing -> pure ()

    exitSuccess
