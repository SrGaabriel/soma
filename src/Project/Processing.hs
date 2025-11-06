{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Project.Processing where

import Alloy.Defunc (defunctionalizeModule)
import Alloy.Lower (lowerAlloyModule)
import Alloy.Monomorphize (monomorphizeModule)

import Alloy.CSE (cseModuleGlobal)
import Alloy.HoistAllocas (hoistAllocasModule)
import Alloy.MonadicInline (monadicInlineModule)
import Alloy.PromoteRefs (promoteRefsModule)
import Alloy.ReaderRewrite (readerRewriteModule)
import Alloy.Simplify (simplifyModule)
import Config.Options (Options (..))
import Control.Exception (SomeException, catch)
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.Char8 as BLC
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Inference.Assembler (inferTreeT)
import Inference.Core (TypeMap)
import Inference.Resolver (runResolverWithEnv)
import Llvm.Gen.Entry (runLlvmCodeGenAndTranscribe)
import Logging.ErrorPrinter (printError)
import Logging.PrettyTrees (TreeShow (treeShow))
import Metal.Gen.Entry (compileMetalModule)
import Metal.Lift (liftLambdas)
import Metal.MonadNormalize (normalizeModule)
import Project.Graph (ModuleGraph, buildDependencyGraph)
import Project.Metadata (projectMetadataPublicSymbols)
import Project.Module (ModuleInfo (..))
import Project.Symbols (Symbol (..))
import Project.Tarball (TarballContents (..), createProjectTarball, defaultTarballOptions, extractProjectTarball, tarballExtension)
import Syntax.Tree (Expr (..), exprChildren)
import System.Directory (createDirectoryIfMissing, removeFile)
import System.Directory.Internal.Prelude (exitFailure)
import System.FilePath (takeBaseName, takeDirectory, takeExtension, (<.>), (</>))
import System.Process (callProcess)
import Typing.Types (QualifiedType)

extractSymbolImports :: Expr -> [(String, [String])]
extractSymbolImports (ExprRoot cs) = concatMap extractSymbolImports cs
extractSymbolImports (ExprImport name elements _) =
    [(name, elements)]
extractSymbolImports e = concatMap extractSymbolImports (exprChildren e)

wordsWhen :: (Char -> Bool) -> String -> [String]
wordsWhen p s = case dropWhile p s of
    "" -> []
    s' -> w : wordsWhen p s''
      where
        (w, s'') = break p s'

filterSymbolsByNames :: [String] -> Map.Map Symbol QualifiedType -> Map.Map Symbol QualifiedType
filterSymbolsByNames names =
    Map.filterWithKey (\sym _ -> resolvedSymbolName sym `elem` names)

type AllModuleElements = Map.Map String (Expr, TypeMap, Map.Map Symbol QualifiedType)

processModules :: [String] -> ModuleGraph -> Options -> IO ()
processModules sorted graph compileOptions = do
    let inputName = fromMaybe "app" $ optionsName compileOptions
    let mOutputFile = optionsOutput compileOptions
    let isLib = optionsLib compileOptions
    deps <- processExternalDependencies (optionsDeps compileOptions)

    (allModules, fusedTypeMap) <- processAllModules inputName sorted graph Map.empty deps Map.empty
    let fusedAst = createFusedAst allModules
    let metallic = compileMetalModule inputName fusedAst fusedTypeMap
    putStrLn $ "Metal module compiled:\n" ++ treeShow metallic

    let metallicLifted = liftLambdas metallic
    putStrLn $ "Metal module after lambda lifting:\n" ++ treeShow metallicLifted

    let metallicNormalized = normalizeModule metallicLifted
    let alloy = lowerAlloyModule inputName metallicNormalized
    let alloyMono = monomorphizeModule alloy
    let alloyDefunc = defunctionalizeModule alloyMono
    let alloyReader = readerRewriteModule alloyDefunc
    let alloyInlined = monadicInlineModule alloyReader
    let alloyHoisted = hoistAllocasModule alloyInlined

    let optimizeFixpoint m =
            let step x = simplifyModule (promoteRefsModule (cseModuleGlobal x))
                x' = step m
            in if x' == m then m else optimizeFixpoint x'

    let alloyOpt = optimizeFixpoint alloyHoisted

    putStrLn $ "Alloy module (MIR) compiled (pre-mono):\n" ++ treeShow alloy
    putStrLn $ "Alloy module (MIR) monomorphized + inlined + simplified (fixpoint):\n" ++ treeShow alloyOpt

    let llvmIr = runLlvmCodeGenAndTranscribe alloyOpt

    let outputFile = fromMaybe inputName mOutputFile
    let outputName = takeBaseName outputFile

    let outputExt = takeExtension outputFile
    let outputDir = takeDirectory outputFile

    createDirectoryIfMissing True outputDir

    case outputExt of
        ".ll" -> do
            writeFile outputFile llvmIr
            putStrLn $ "Generated LLVM IR file: " ++ outputFile
        ".o" -> do
            let llTemp = outputDir </> outputName <.> "ll"
            writeFile llTemp llvmIr
            putStrLn $ "Generated temporary LLVM IR file: " ++ llTemp
            catch
                ( do
                    callProcess "llc" ["-filetype=obj", llTemp, "-o", outputFile]
                    putStrLn $ "Generated object file: " ++ outputFile
                )
                ( \(_ :: SomeException) -> do
                    putStrLn "llc not found or object compilation failed. To compile manually, run:"
                    putStrLn $ "llc -filetype=obj " ++ llTemp ++ " -o " ++ outputFile
                    exitFailure
                )
        ext | ext == tarballExtension -> do
            let llFile = outputDir </> outputName <.> "ll"
            let objFile = outputDir </> outputName <.> "o"

            writeFile llFile llvmIr
            putStrLn $ "Generated LLVM IR file: " ++ llFile

            objFileExists <-
                catch
                    ( do
                        callProcess "llc" ["-filetype=obj", llFile, "-o", objFile]
                        putStrLn $ "Generated object file: " ++ objFile
                        return True
                    )
                    ( \(_ :: SomeException) -> do
                        putStrLn "Warning: llc not found, tarball will not include object file"
                        return False
                    )

            objContentBS <-
                if objFileExists
                    then BL.readFile objFile
                    else return BL.empty
            let objContent = BLC.unpack objContentBS

            let publicSymbols = Map.unions [syms | (_, _, syms) <- Map.elems allModules]
            let depGraph = buildDependencyGraph graph
            let sourceFiles = [modulePath info | info <- Map.elems graph]

            let objFiles = ([(objFile, objContent) | objFileExists])
            createProjectTarball
                outputFile
                defaultTarballOptions
                inputName
                "0.1.0"
                sourceFiles
                publicSymbols
                depGraph
                objFiles
                [(llFile, llvmIr)]

            -- todo: undoc catch (removeFile llFile) (\(_ :: SomeException) -> return ())
            catch (removeFile objFile) (\(_ :: SomeException) -> return ())
        ""
            | isLib -> do
                putStrLn "Can't build executable for library"
                exitFailure
            | not isLib -> do
                let llTemp = outputFile <.> "ll"
                writeFile llTemp llvmIr
                putStrLn $ "Generated temporary LLVM IR file: " ++ llTemp
                catch
                    ( do
                        callProcess "clang" ["-o", outputFile, llTemp]
                        putStrLn $ "Successfully compiled executable: " ++ outputFile
                    )
                    ( \(_ :: SomeException) -> do
                        putStrLn "clang not found or compilation failed. To compile manually, run:"
                        putStrLn $ "clang -o " ++ outputFile ++ " " ++ llTemp
                        exitFailure
                    )
        ext -> do
            putStrLn $ "Unknown output extension: " ++ ext
            exitFailure

    putStrLn "✅ Build process completed."

processAllModules :: String -> [String] -> ModuleGraph -> AllModuleElements -> Map.Map String (Map.Map Symbol QualifiedType) -> TypeMap -> IO (AllModuleElements, TypeMap)
processAllModules _ [] _ allModules _ fusedTypeMap = return (allModules, fusedTypeMap)
processAllModules packageName (modName : rest) graph allModules deps fusedTypeMap = do
    let Just modInfo = Map.lookup modName graph
        ast = moduleAst modInfo

    let imports = extractSymbolImports ast
        seedEnv =
            Map.unions
                $ map
                    ( \(impMod, mSyms) ->
                        case Map.lookup impMod allModules of
                            Just (_, _, modEnv) -> filterSymbolsByNames mSyms modEnv
                            Nothing ->
                                let properModuleName = takeWhile (/= '/') impMod
                                in maybe
                                    Map.empty
                                    (filterSymbolsByNames mSyms)
                                    (Map.lookup properModuleName deps)
                    )
                    imports

    resolvedResult <- runResolverWithEnv packageName modName seedEnv ast
    (resolvedAst, fullEnv, _instanceEnv) <- case resolvedResult of
        Left err -> printError err (modulePath modInfo) (moduleContent modInfo) "ANALYSIS" >> exitFailure
        Right res -> return res

    let newDefs = Map.difference fullEnv seedEnv

    typesResult <- inferTreeT packageName modName fullEnv resolvedAst
    types <- case typesResult of
        Left errs -> mapM_ (\e -> printError e (modulePath modInfo) (moduleContent modInfo) "INFERENCE") errs >> exitFailure
        Right t -> return t

    putStrLn $ "Module " ++ modName ++ " processed successfully: "
    putStrLn $ treeShow types

    let newAllModules = Map.insert modName (resolvedAst, types, newDefs) allModules
        newFusedTypeMap = Map.union types fusedTypeMap
    processAllModules packageName rest graph newAllModules deps newFusedTypeMap

createFusedAst :: Map.Map String (Expr, TypeMap, Map.Map Symbol QualifiedType) -> Expr
createFusedAst allModules =
    let allExprs =
            concatMap
                ( \(ast, _, _) -> case ast of
                    ExprRoot exprs -> exprs
                    singleExpr -> [singleExpr]
                )
                (Map.elems allModules)
    in ExprRoot allExprs

processExternalDependencies :: [(String, String)] -> IO (Map.Map String (Map.Map Symbol QualifiedType))
processExternalDependencies externals = do
    list <-
        mapM
            ( \(name, path) -> do
                tarball <- extractProjectTarball path
                case tarball of
                    Left err -> error $ "Failed to extract external dependency " ++ name ++ ": " ++ err
                    Right (TarballContents{tcMetadata}) -> do
                        let exports = projectMetadataPublicSymbols tcMetadata
                        pure (name, exports)
            )
            externals
    pure $ Map.fromList list
