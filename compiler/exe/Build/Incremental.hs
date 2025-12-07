{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Build.Incremental (
    processModulesIncremental,
    processExternalDependencies,
) where

import Alloy.CSE (cseModuleGlobal)
import Alloy.Defunc (defunctionalizeModule)
import Alloy.ExpandIntrinsics (expandIntrinsicsModule)
import Alloy.HoistAllocas (hoistAllocasModule)
import Alloy.Inline (defaultInlineConfig, inlineModule)
import Alloy.Ir (AlloyModule (..))
import Alloy.MonadicInline (monadicInlineModule)
import Alloy.Monomorphize (monomorphizeModule)
import Alloy.PromoteRefs (promoteRefsModule)
import Alloy.ReaderRewrite (readerRewriteModule)
import Alloy.Simplify (forwardClosureEnvValuesModule, simplifyModule)
import Build.Metadata (SerializableConstructorMetadata, SerializableName, constructorMetadataToSerializable, nameToSerializable, projectMetadataConstructors, projectMetadataInstances, projectMetadataPublicSymbols, serializableToConstructorMetadata, serializableToName)
import Build.Tarball (TarballContents (TarballContents, tcAlloyModules, tcMetadata), createProjectTarball, defaultTarballOptions, extractProjectTarball, tarballExtension)
import Circuit.Linearize (linearizeModule)
import Circuit.Lower (lowerModule)
import Circuit.Parallel (defaultParallelConfig, parallelizeModule)
import qualified Circuit.Simplify as CS
import Circuit.ToAlloy (lowerCircuitToAlloy)
import Circuit.ToGraph (lowerCircuitToGraph)
import Circuit.Validate (validateModule)
import Config.Options (CompilationMode (..), Options (..))
import Control.Exception (SomeException, catch)
import Control.Monad (unless, when)
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.Char8 as BLC
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Format.Trees (prettyPrintAst, treeShow)
import Inference.Core (InstanceEnv)
import Llvm.Gen.Entry (runLlvmCodeGenAndTranscribe)
import Logging.Errors (printError)
import Logging.Trees (prettyCircuit)
import Metal.Gen.Entry (TypedLowerResult (..), compileMetalModule)
import Metal.Gen.Metadata (extractConstructorMetadata)
import Metal.Lift (liftLambdas)
import Metal.Lower (LowerResult (..))
import Metal.Module (MetallicModule (..))
import Metal.MonadNormalize (normalizeModule)
import Project.Check (CheckedModule (..), checkModule)
import Project.Graph
import Project.Module
import Project.Symbols (Symbol (..), SymbolKind (..))
import Metal.Lower (symbolToName)
import Syntax.Tree (Expr (..))
import System.Directory
import System.Exit (exitFailure)
import System.FilePath
import System.Process (callProcess)
import Typing.Types (QualifiedType)

data CompiledModule = CompiledModule
    { cmModuleName :: ModuleName
    , cmMetallicNormalized :: MetallicModule
    , cmAlloyExpanded :: AlloyModule
    , cmPublicSymbols :: Map Symbol QualifiedType
    , cmPublicInstances :: InstanceEnv
    , cmResolvedAst :: Expr
    }
    deriving (Show)

compileModuleSeparately ::
    String ->
    ModuleInfo ->
    Map ModuleName CompiledModule ->
    Map String (Map Symbol QualifiedType) ->
    Map String InstanceEnv ->
    Map SerializableName SerializableConstructorMetadata ->
    Options ->
    IO CompiledModule
compileModuleSeparately packageName modInfo compiledDeps externalDeps externalInstances externalConstructors options = do
    let modName = moduleName modInfo

    putStrLn $ "Compiling module: " ++ modName

    let checkedDeps =
            Map.map
                ( \c ->
                    CheckedModule
                        { checkedModuleName = cmModuleName c
                        , checkedResolvedAst = cmResolvedAst c
                        , checkedLowerResult = LowerResult [] [] [] []
                        , checkedTypedBindings = []
                        , checkedTypedInstances = []
                        , checkedPublicSymbols = cmPublicSymbols c
                        , checkedInstances = cmPublicInstances c
                        }
                )
                compiledDeps

    let metallicConstructors = Map.mapKeys serializableToName $ Map.map serializableToConstructorMetadata externalConstructors
    let (allErrors, checked) = checkModule packageName modInfo checkedDeps externalDeps externalInstances metallicConstructors

    putStrLn "Resolved AST:"
    prettyPrintAst (checkedResolvedAst checked)
    putStrLn $ "Module " ++ modName ++ " type checked"

    unless (null allErrors) $ do
        putStrLn $ "Errors while compiling module " ++ modName ++ ":"
        mapM_ (\e -> printError e (modulePath modInfo) (moduleContent modInfo) "INFERENCE") allErrors
        exitFailure

    let resolvedAst = checkedResolvedAst checked
        lowerResult = checkedLowerResult checked
        typedBindings = checkedTypedBindings checked
        typedInstances = checkedTypedInstances checked
        newDefs = checkedPublicSymbols checked
        instanceEnv = checkedInstances checked

    let typedLowerResult =
            TypedLowerResult
                { tlrBindings = typedBindings
                , tlrTypes = lrTypes lowerResult
                , tlrInstances = typedInstances
                , tlrTypeClasses = lrTypeClasses lowerResult
                }

    let metallicExternalConstructors = Map.mapKeys serializableToName $ Map.map serializableToConstructorMetadata externalConstructors
    let intrinsicSymbols = Map.keys $ Map.filterWithKey (\sym _ -> resolvedSymbolKind sym == IntrinsicBindingSymbol) newDefs
        intrinsicNames = Set.fromList $ map symbolToName intrinsicSymbols
    let metallic = compileMetalModule modName typedLowerResult metallicExternalConstructors
        metallicLifted = liftLambdas intrinsicNames metallic
        metallicNormalized = normalizeModule metallicLifted

    putStrLn $ "Metal (HIR) complete for " ++ modName
    putStrLn $ treeShow metallicNormalized

    -- Lower to Circuit IR
    let circuitModule = lowerModule metallicNormalized
        circuitSimplified = CS.simplifyModule circuitModule

    -- Lower to Alloy MIR
    let linearizedCircuit = linearizeModule circuitSimplified
    case optionsMode options of
        ModeGraph -> putStrLn "=== Circuit IR (graph mode - linearized) ==="
        _ -> putStrLn "=== Circuit IR (after linearization) ==="
    putStrLn $ prettyCircuit linearizedCircuit

    when (optionsValidateCircuit options)
        $ let validationErrors = validateModule linearizedCircuit
          in unless (null validationErrors) $ do
                putStrLn $ "Circuit validation errors in module " ++ modName ++ ":"
                mapM_ (putStrLn . ("- " ++) . show) validationErrors
                exitFailure

    let alloyFromCircuit = case optionsMode options of
            ModeGraph ->
                -- Linearized graph mode: linearize first, then use graph reduction
                lowerCircuitToGraph linearizedCircuit
            ModeStandard ->
                -- Standard mode: linearize for compile-time memory management
                lowerCircuitToAlloy linearizedCircuit
            ModeHybrid ->
                -- Hybrid mode: linearize for compile-time memory management and then parallelize
                let parallelConfig = defaultParallelConfig
                    circuitParallelized = parallelizeModule parallelConfig linearizedCircuit
                in lowerCircuitToAlloy circuitParallelized

        alloyExpanded = expandIntrinsicsModule alloyFromCircuit

    putStrLn $ "Alloy (MIR) complete for " ++ modName
    putStrLn $ treeShow alloyExpanded

    return
        $ CompiledModule
            { cmModuleName = modName
            , cmMetallicNormalized = metallicNormalized
            , cmAlloyExpanded = alloyExpanded
            , cmPublicSymbols = newDefs
            , cmPublicInstances = instanceEnv
            , cmResolvedAst = resolvedAst
            }

linkCompiledModules ::
    String ->
    [CompiledModule] ->
    Map SerializableName SerializableConstructorMetadata ->
    [AlloyModule] ->
    IO (AlloyModule, Map SerializableName SerializableConstructorMetadata)
linkCompiledModules packageName compiledModules externalConstructors externalAlloyModules = do
    putStrLn "\n=== Starting link-time optimization phase ==="

    let localAlloyModules = map cmAlloyExpanded compiledModules
    let allAlloyModules = localAlloyModules ++ externalAlloyModules

    let (fusedAst, fusedSymbols) = createFusedAst [(cmResolvedAst cm, cmPublicSymbols cm) | cm <- compiledModules]
        localConstructors = extractConstructorMetadata fusedSymbols fusedAst
        allConstructors = Map.union externalConstructors (Map.mapKeys nameToSerializable $ Map.map constructorMetadataToSerializable localConstructors)

    let fusedAlloy = concatenateAlloyModules packageName allAlloyModules

    let alloyMono = monomorphizeModule fusedAlloy
        alloyDefunc = defunctionalizeModule alloyMono
        alloyUserInlined = inlineModule defaultInlineConfig alloyDefunc
        alloyReader = readerRewriteModule alloyUserInlined
        alloyInlined = monadicInlineModule alloyReader
        alloyHoisted = hoistAllocasModule alloyInlined

    let optimizeFixpoint m =
            let step x = simplifyModule (forwardClosureEnvValuesModule (promoteRefsModule (cseModuleGlobal x)))
                x' = step m
            in if x' == m then m else optimizeFixpoint x'

    let alloyOpt = optimizeFixpoint alloyHoisted

    putStrLn "Link-time optimization complete"
    putStrLn $ treeShow alloyOpt

    return (alloyOpt, allConstructors)

concatenateAlloyModules :: String -> [AlloyModule] -> AlloyModule
concatenateAlloyModules packageName modules =
    AlloyModule
        { amName = packageName
        , amFunctions = concatMap amFunctions modules
        , amDictionaries = concatMap amDictionaries modules
        , amTypeClasses = concatMap amTypeClasses modules
        }

createFusedAst :: [(Expr, Map Symbol QualifiedType)] -> (Expr, Map Symbol QualifiedType)
createFusedAst allModules =
    let allExprs =
            concatMap
                ( \(ast, _) -> case ast of
                    ExprRoot exprs -> exprs
                    singleExpr -> [singleExpr]
                )
                allModules
        allSymbols = Map.unions (map snd allModules)
    in (ExprRoot allExprs, allSymbols)

processModulesIncremental :: [String] -> ModuleGraph -> Options -> IO ()
processModulesIncremental sorted graph compileOptions = do
    let inputName = fromMaybe "app" $ optionsName compileOptions

    (externalDeps, externalInstances, externalConstructors, externalAlloyModules) <-
        processExternalDependencies (optionsDeps compileOptions)

    compiledModules <-
        compileAllModulesInOrder
            sorted
            graph
            Map.empty
            externalDeps
            externalInstances
            externalConstructors
            inputName
            compileOptions

    putStrLn $ "\n Compiled " ++ show (length compiledModules) ++ " modules separately"
    (alloyOpt, allCtorsForCodeGen) <- linkCompiledModules inputName compiledModules externalConstructors externalAlloyModules

    let llvmIr = runLlvmCodeGenAndTranscribe alloyOpt
    generateOutputFile inputName llvmIr compileOptions compiledModules graph allCtorsForCodeGen

    putStrLn "Build process completed."

compileAllModulesInOrder ::
    [ModuleName] ->
    ModuleGraph ->
    Map ModuleName CompiledModule ->
    Map String (Map Symbol QualifiedType) ->
    Map String InstanceEnv ->
    Map SerializableName SerializableConstructorMetadata ->
    String ->
    Options ->
    IO [CompiledModule]
compileAllModulesInOrder [] _ _ _ _ _ _ _ = return []
compileAllModulesInOrder (modName : rest) graph compiled externalDeps externalInstances externalConstructors packageName options = do
    let Just modInfo = Map.lookup modName graph

    compiledModule <-
        compileModuleSeparately
            packageName
            modInfo
            compiled
            externalDeps
            externalInstances
            externalConstructors
            options

    let newCompiled = Map.insert modName compiledModule compiled

    restModules <-
        compileAllModulesInOrder
            rest
            graph
            newCompiled
            externalDeps
            externalInstances
            externalConstructors
            packageName
            options
    return (compiledModule : restModules)

generateOutputFile ::
    String ->
    String ->
    Options ->
    [CompiledModule] ->
    ModuleGraph ->
    Map SerializableName SerializableConstructorMetadata ->
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
        ext
            | ext == tarballExtension -> do
                let llFile = outputDir </> outputName <.> "ll"
                writeFile llFile llvmIr

                let publicSymbols = Map.unions [cmPublicSymbols cm | cm <- compiledModules]
                    publicInstances = Map.unions [cmPublicInstances cm | cm <- compiledModules]
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
                    (Map.toList publicInstances)
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
                let runtimeLibPath = case optionsMode compileOptions of
                        ModeGraph -> "runtime/inets_soma.a"
                        ModeHybrid -> "runtime/hybrid_soma.a"
                        ModeStandard -> "runtime/native_soma.a"

                runtimeExists <- doesFileExist runtimeLibPath
                unless runtimeExists $ do
                    putStrLn $ "Warning: C runtime not found at " ++ runtimeLibPath
                    putStrLn "Building runtime library..."
                    catch
                        (callProcess "make" ["-C", "runtime"])
                        ( \(_ :: SomeException) -> do
                            putStrLn "Failed to build runtime. Please run: cd runtime && make"
                            exitFailure
                        )

                let llTemp = outputFile <.> "ll"
                writeFile llTemp llvmIr
                catch
                    ( do
                        let optimizationArgs = case optionsOptimizationLevel compileOptions of
                                Just 3 ->
                                    [ "-O3"
                                    , "-march=native"
                                    , "-mtune=native"
                                    , "-flto"
                                    , "-fomit-frame-pointer"
                                    , "-fno-exceptions"
                                    , "-fno-unwind-tables"
                                    ]
                                _ -> []
                        let commandArgs = optimizationArgs ++ ["-o", outputFile, llTemp, runtimeLibPath]
                        callProcess "clang" commandArgs
                        putStrLn $ "Ran: " ++ unwords ("clang" : commandArgs)
                        putStrLn $ "Successfully compiled executable: " ++ outputFile
                        putStrLn $ "(Linked with C runtime: " ++ runtimeLibPath ++ ")"
                    )
                    ( \(_ :: SomeException) -> do
                        putStrLn "clang not found. To compile manually:"
                        putStrLn $ "clang -o " ++ outputFile ++ " " ++ llTemp ++ " " ++ runtimeLibPath
                        exitFailure
                    )
        ext -> do
            putStrLn $ "Unknown output extension: " ++ ext
            exitFailure

processExternalDependencies :: [(String, String)] -> IO (Map.Map String (Map.Map Symbol QualifiedType), Map.Map String InstanceEnv, Map.Map SerializableName SerializableConstructorMetadata, [AlloyModule])
processExternalDependencies externals = do
    list <-
        mapM
            ( \(name, path) -> do
                tarball <- extractProjectTarball path
                case tarball of
                    Left err -> error $ "Failed to extract external dependency " ++ name ++ ": " ++ err
                    Right (TarballContents{tcMetadata, tcAlloyModules}) -> do
                        let exports = projectMetadataPublicSymbols tcMetadata
                        let instances = projectMetadataInstances tcMetadata
                        let constructors = projectMetadataConstructors tcMetadata
                        pure (name, exports, instances, constructors, tcAlloyModules)
            )
            externals
    let allExports = Map.unions [exports | (_, exports, _, _, _) <- list]
        groupedByModule =
            Map.fromListWith
                Map.union
                [ (resolvedSymbolModule sym, Map.singleton sym ty)
                | (sym, ty) <- Map.toList allExports
                ]
    let instancesByModule =
            Map.fromListWith
                Map.union
                [ (modName, insts)
                | (_, exports, insts, _, _) <- list
                , let modNames = Set.toList $ Set.fromList [resolvedSymbolModule sym | sym <- Map.keys exports]
                , modName <- modNames
                ]
    let constructors = Map.unions [ctors | (_, _, _, ctors, _) <- list]
    let externalAlloy = concat [modules | (_, _, _, _, modules) <- list]
    pure (groupedByModule, instancesByModule, constructors, externalAlloy)
