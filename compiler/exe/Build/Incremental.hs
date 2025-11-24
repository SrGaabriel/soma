{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Build.Incremental where

import Alloy.CSE (cseModuleGlobal)
import Alloy.Defunc (defunctionalizeModule)
import Alloy.ExpandIntrinsics (expandIntrinsicsModule)
import Alloy.HoistAllocas (hoistAllocasModule)
import Alloy.Ir (AlloyModule (..))
import Alloy.Lower (lowerAlloyModule)
import Alloy.MonadicInline (monadicInlineModule)
import Alloy.Monomorphize (monomorphizeModule)
import Alloy.PromoteRefs (promoteRefsModule)
import Alloy.ReaderRewrite (readerRewriteModule)
import Alloy.Simplify (simplifyModule)
import Build.Metadata (SerializableConstructorMetadata, projectMetadataConstructors, projectMetadataPublicSymbols)
import Build.Tarball (TarballContents (TarballContents, tcAlloyModules, tcMetadata), createProjectTarball, defaultTarballOptions, extractProjectTarball, tarballExtension)
import Config.Options (Options (..))
import Control.Exception (SomeException, catch)
import Control.Monad (unless)
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.Char8 as BLC
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Inference.Assembler (inferTree)
import Inference.Core (TypeMap)
import Inference.Resolver (runResolverWithEnv)
import Llvm.Gen.Entry (runLlvmCodeGenAndTranscribe)
import Logging.Errors (printError)
import Metal.Gen.Entry (compileMetalModule)
import Metal.Gen.Metadata (constructorMetadataToSerializable, extractConstructorMetadata, serializableToConstructorMetadata)
import Metal.Lift (liftLambdas)
import Metal.Module
import Metal.MonadNormalize (normalizeModule)
import Project.Extracts (extractSymbolImports, filterSymbolsByNames)
import Project.Graph
import Project.Module
import Project.Symbols (Symbol)
import Syntax.Tree (Expr (ExprRoot))
import System.Directory
import System.Exit (exitFailure)
import System.FilePath
import System.Process (callProcess)
import Typing.Types (QualifiedType)

data CompiledModule = CompiledModule
    { cmModuleName :: ModuleName
    , cmMetallicNormalized :: MetallicModule -- after lambda lifting & normalization
    , cmAlloyExpanded :: AlloyModule -- after intrinsic expansion (pre-dictionary/mono)
    , cmTypeMap :: TypeMap
    , cmPublicSymbols :: Map Symbol QualifiedType
    , cmResolvedAst :: Expr
    }
    deriving (Show)

compileModuleSeparately ::
    String ->
    ModuleInfo ->
    Map ModuleName CompiledModule ->
    Map String (Map Symbol QualifiedType) ->
    Map String SerializableConstructorMetadata ->
    IO CompiledModule
compileModuleSeparately packageName modInfo compiledDeps externalDeps externalConstructors = do
    let modName = moduleName modInfo
        ast = moduleAst modInfo

    putStrLn $ "Compiling module: " ++ modName

    let imports = extractSymbolImports ast
        seedEnv = Map.unions $ map resolveImport imports

    let (resolverErrors, (resolvedAst, fullEnv, instanceEnv)) = runResolverWithEnv packageName modName seedEnv ast
    let (inferenceErrors, types) = inferTree packageName modName fullEnv instanceEnv resolvedAst
    let newDefs = Map.difference fullEnv seedEnv

    let allErrors = resolverErrors ++ inferenceErrors
    unless (null allErrors) $ do
        putStrLn $ "Errors while compiling module " ++ modName ++ ":"
        mapM_ (\e -> printError e (modulePath modInfo) (moduleContent modInfo) "INFERENCE") allErrors
        exitFailure

    putStrLn $ "Module " ++ modName ++ " type checked"

    let metallicExternalConstructors = Map.map serializableToConstructorMetadata externalConstructors
    let metallic = compileMetalModule modName resolvedAst types metallicExternalConstructors
        metallicLifted = liftLambdas metallic
        metallicNormalized = normalizeModule metallicLifted

    putStrLn $ "Metal (HIR) complete for " ++ modName

    let alloyPreDictMono = lowerAlloyModule modName metallicNormalized
        alloyExpanded = expandIntrinsicsModule alloyPreDictMono

    putStrLn $ "Alloy (MIR) complete for " ++ modName

    return
        $ CompiledModule
            { cmModuleName = modName
            , cmMetallicNormalized = metallicNormalized
            , cmAlloyExpanded = alloyExpanded
            , cmTypeMap = types
            , cmPublicSymbols = newDefs
            , cmResolvedAst = resolvedAst
            }
  where
    resolveImport (impMod, mSyms) =
        case Map.lookup impMod compiledDeps of
            Just compiled -> filterSymbolsByNames mSyms (cmPublicSymbols compiled)
            Nothing ->
                let properModuleName = takeWhile (/= '/') impMod
                in maybe Map.empty (filterSymbolsByNames mSyms) (Map.lookup properModuleName externalDeps)

linkCompiledModules ::
    String ->
    [CompiledModule] ->
    Map String SerializableConstructorMetadata ->
    [AlloyModule] ->
    IO (AlloyModule, Map String SerializableConstructorMetadata)
linkCompiledModules packageName compiledModules externalConstructors externalAlloyModules = do
    putStrLn "\n=== Starting link-time optimization phase ==="

    let localAlloyModules = map cmAlloyExpanded compiledModules
    let allAlloyModules = localAlloyModules ++ externalAlloyModules

    let fusedAst = createFusedAst [(cmResolvedAst cm, cmTypeMap cm, cmPublicSymbols cm) | cm <- compiledModules]
        localConstructors = extractConstructorMetadata fusedAst
        allConstructors = Map.union externalConstructors (Map.map constructorMetadataToSerializable localConstructors)

    let fusedAlloy = concatenateAlloyModules packageName allAlloyModules

    -- todo: fix dicts
    let
        -- alloyWithDicts = transformModuleWithDictionaries fusedAlloy
        alloyMono = monomorphizeModule fusedAlloy
        alloyDefunc = defunctionalizeModule alloyMono
        alloyReader = readerRewriteModule alloyDefunc
        alloyInlined = monadicInlineModule alloyReader
        alloyHoisted = hoistAllocasModule alloyInlined

    let optimizeFixpoint m =
            let step x = simplifyModule (promoteRefsModule (cseModuleGlobal x))
                x' = step m
            in if x' == m then m else optimizeFixpoint x'

    let alloyOpt = optimizeFixpoint alloyHoisted

    putStrLn "Link-time optimization complete"

    return (alloyOpt, allConstructors)

concatenateAlloyModules :: String -> [AlloyModule] -> AlloyModule
concatenateAlloyModules packageName modules =
    AlloyModule
        { amName = packageName
        , amFunctions = concatMap amFunctions modules
        , amDictionaries = concatMap amDictionaries modules
        , amTypeClasses = concatMap amTypeClasses modules
        }

createFusedAst :: [(Expr, TypeMap, Map Symbol QualifiedType)] -> Expr
createFusedAst allModules =
    let allExprs =
            concatMap
                ( \(ast, _, _) -> case ast of
                    ExprRoot exprs -> exprs
                    singleExpr -> [singleExpr]
                )
                allModules
    in ExprRoot allExprs

processModulesIncremental :: [String] -> ModuleGraph -> Options -> IO ()
processModulesIncremental sorted graph compileOptions = do
    let inputName = fromMaybe "app" $ optionsName compileOptions

    (externalDeps, externalConstructors, externalAlloyModules) <- processExternalDependencies (optionsDeps compileOptions)

    compiledModules <- compileAllModulesInOrder sorted graph Map.empty externalDeps externalConstructors inputName

    putStrLn $ "\n✅ Compiled " ++ show (length compiledModules) ++ " modules separately"

    (alloyOpt, allCtorsForCodeGen) <- linkCompiledModules inputName compiledModules externalConstructors externalAlloyModules

    let llvmIr = runLlvmCodeGenAndTranscribe alloyOpt

    generateOutputFile inputName llvmIr compileOptions compiledModules graph allCtorsForCodeGen

    putStrLn "✅ Build process completed."

compileAllModulesInOrder ::
    [ModuleName] ->
    ModuleGraph ->
    Map ModuleName CompiledModule ->
    Map String (Map Symbol QualifiedType) ->
    Map String SerializableConstructorMetadata ->
    String ->
    IO [CompiledModule]
compileAllModulesInOrder [] _ _ _ _ _ = return []
compileAllModulesInOrder (modName : rest) graph compiled externalDeps externalConstructors packageName = do
    let Just modInfo = Map.lookup modName graph

    compiledModule <- compileModuleSeparately packageName modInfo compiled externalDeps externalConstructors

    let newCompiled = Map.insert modName compiledModule compiled

    restModules <- compileAllModulesInOrder rest graph newCompiled externalDeps externalConstructors packageName
    return (compiledModule : restModules)

generateOutputFile ::
    String ->
    String ->
    Options ->
    [CompiledModule] ->
    ModuleGraph ->
    Map String SerializableConstructorMetadata ->
    IO ()
generateOutputFile inputName llvmIr compileOptions compiledModules graph allConstructors = do
    let mOutputFile = optionsOutput compileOptions
        isLib = optionsLib compileOptions
        outputFile = fromMaybe inputName mOutputFile
        outputName = takeBaseName outputFile
        outputExt = takeExtension outputFile
        outputDir = takeDirectory outputFile

    createDirectoryIfMissing True outputDir

    case outputExt of
        ".ll" -> do
            writeFile outputFile llvmIr
            putStrLn $ "Generated LLVM IR file: " ++ outputFile
        ".o" -> do
            let llTemp = outputDir </> outputName <.> "ll"
            writeFile llTemp llvmIr
            catch
                ( do
                    callProcess "llc" ["-filetype=obj", llTemp, "-o", outputFile]
                    putStrLn $ "Generated object file: " ++ outputFile
                )
                ( \(_ :: SomeException) -> do
                    putStrLn "llc not found. To compile manually:"
                    putStrLn $ "llc -filetype=obj " ++ llTemp ++ " -o " ++ outputFile
                    exitFailure
                )
        ext | ext == tarballExtension -> do
            let llFile = outputDir </> outputName <.> "ll"
            writeFile llFile llvmIr

            let publicSymbols = Map.unions [cmPublicSymbols cm | cm <- compiledModules]
                depGraph = buildDependencyGraph graph
                sourceFiles = [modulePath info | info <- Map.elems graph]

            let objFile = outputDir </> outputName <.> "o"
            objFileExists <-
                catch
                    ( do
                        callProcess "llc" ["-filetype=obj", llFile, "-o", objFile]
                        return True
                    )
                    (\(_ :: SomeException) -> return False)

            objContent <- BL.readFile objFile
            let alloyModulesToSave = map cmAlloyExpanded compiledModules

            createProjectTarball
                outputFile
                defaultTarballOptions
                inputName
                "0.1.0"
                sourceFiles
                publicSymbols
                depGraph
                allConstructors
                [(objFile, objContent) | objFileExists]
                [(llFile, BLC.pack llvmIr)]
                alloyModulesToSave

            catch (removeFile objFile) (\(_ :: SomeException) -> return ())
        ""
            | isLib -> do
                putStrLn "Can't build executable for library"
                exitFailure
            | not isLib -> do
                let llTemp = outputFile <.> "ll"
                writeFile llTemp llvmIr
                catch
                    ( do
                        callProcess "clang" ["-o", outputFile, llTemp]
                        putStrLn $ "Successfully compiled executable: " ++ outputFile
                    )
                    ( \(_ :: SomeException) -> do
                        putStrLn "clang not found. To compile manually:"
                        putStrLn $ "clang -o " ++ outputFile ++ " " ++ llTemp
                        exitFailure
                    )
        ext -> do
            putStrLn $ "Unknown output extension: " ++ ext
            exitFailure

processExternalDependencies :: [(String, String)] -> IO (Map.Map String (Map.Map Symbol QualifiedType), Map.Map String SerializableConstructorMetadata, [AlloyModule])
processExternalDependencies externals = do
    list <-
        mapM
            ( \(name, path) -> do
                tarball <- extractProjectTarball path
                case tarball of
                    Left err -> error $ "Failed to extract external dependency " ++ name ++ ": " ++ err
                    Right (TarballContents{tcMetadata, tcAlloyModules}) -> do
                        let exports = projectMetadataPublicSymbols tcMetadata
                        let constructors = projectMetadataConstructors tcMetadata
                        pure (name, exports, constructors, tcAlloyModules)
            )
            externals
    let symbols = Map.fromList [(name, exports) | (name, exports, _, _) <- list]
    let constructors = Map.unions [ctors | (_, _, ctors, _) <- list]
    let externalAlloy = concat [modules | (_, _, _, modules) <- list]
    pure (symbols, constructors, externalAlloy)
