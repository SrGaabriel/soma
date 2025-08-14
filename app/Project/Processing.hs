{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Project.Processing where

import qualified Data.Map as Map
import Inference.Resolver (runResolverWithEnv)
import Logging.ErrorPrinter (printError)
import Project.Graph (ModuleGraph)
import Project.Module (ModuleInfo (..))
import Syntax.Tree (Expr (..), exprChildren)
import System.Directory.Internal.Prelude (exitFailure)
import Inference.Assembler (inferTreeT)
import Llvm.Gen.Entry (runLlvmCodeGenAndTranscribe)
import Inference.Core (TypeMap)
import Typing.Types (QualifiedType)
import System.Directory (createDirectoryIfMissing)
import System.FilePath ((</>))
import System.Process (callProcess)
import Project.Symbols (Symbol(..))
import Control.Exception (catch, SomeException)
import Logging.PrettyTrees (TreeShow(treeShow))

extractSymbolImports :: Expr -> [(String, Maybe [String])]
extractSymbolImports (ExprRoot cs) = concatMap extractSymbolImports cs
extractSymbolImports (ExprImport name _) =
    let (m, rest) = break (== ':') name
    in if take 2 rest == "::"
        then
            let syms = drop 2 rest
            in [(m, Just (wordsWhen (== ',') syms))]
        else [(name, Nothing)]
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

processModules :: [String] -> ModuleGraph -> String -> FilePath -> IO ()
processModules sorted graph outputBaseName inputPath = do
    (allModules, fusedTypeMap) <- processAllModules sorted graph Map.empty Map.empty
    
    let fusedAst = createFusedAst allModules
    let llvmIr = runLlvmCodeGenAndTranscribe outputBaseName fusedAst fusedTypeMap
    
    let buildDir = inputPath </> "build"
    createDirectoryIfMissing True buildDir

    let llFile = buildDir </> (outputBaseName ++ ".ll")
    let exeFile = buildDir </> outputBaseName

    writeFile llFile llvmIr
    putStrLn $ "Generated LLVM IR file: " ++ llFile
    
    result <- catch (do
        callProcess "clang" ["-o", exeFile, llFile]
        putStrLn $ "Successfully compiled executable: " ++ exeFile
        return True
        ) (\(_ :: SomeException) -> do
            putStrLn $ "clang not found or compilation failed. To compile manually, run:"
            putStrLn $ "clang -o " ++ exeFile ++ " " ++ llFile
            return False
        )

    if result
        then putStrLn "✅ Build completed successfully."
        else putStrLn "❌ LLVM IR generated. Internal build failure." >> exitFailure

processAllModules :: [String] -> ModuleGraph -> Map.Map String (Expr, TypeMap, Map.Map Symbol QualifiedType) -> TypeMap -> IO (Map.Map String (Expr, TypeMap, Map.Map Symbol QualifiedType), TypeMap)
processAllModules [] _graph allModules fusedTypeMap = return (allModules, fusedTypeMap)
processAllModules (modName : rest) graph allModules fusedTypeMap = do
    let Just modInfo = Map.lookup modName graph
        ast = moduleAst modInfo
    
    let imports = extractSymbolImports ast
        seedEnv = Map.unions $ map
            (\(impMod, mSyms) ->
                case Map.lookup impMod allModules of
                    Just (_, _, modEnv) -> case mSyms of
                        Just syms -> filterSymbolsByNames syms modEnv
                        Nothing -> modEnv
                    Nothing -> Map.empty
            ) imports
    
    resolvedResult <- runResolverWithEnv modName seedEnv ast
    (resolvedAst, fullEnv, _instanceEnv) <- case resolvedResult of
        Left err -> printError err (modulePath modInfo) (moduleContent modInfo) "ANALYSIS" >> exitFailure
        Right res -> return res
    
    let newDefs = Map.difference fullEnv seedEnv
    
    typesResult <- inferTreeT modName fullEnv resolvedAst
    types <- case typesResult of
        Left errs -> mapM_ (\e -> printError e (modulePath modInfo) (moduleContent modInfo) "INFERENCE") errs >> exitFailure
        Right t -> return t
    
    putStrLn $ "Module " ++ modName ++ " processed successfully: "
    putStrLn $ treeShow types

    let newAllModules = Map.insert modName (resolvedAst, types, newDefs) allModules
        newFusedTypeMap = Map.union types fusedTypeMap
    processAllModules rest graph newAllModules newFusedTypeMap

createFusedAst :: Map.Map String (Expr, TypeMap, Map.Map Symbol QualifiedType) -> Expr
createFusedAst allModules = 
    let allExprs = concatMap (\(ast, _, _) -> case ast of
            ExprRoot exprs -> exprs
            singleExpr -> [singleExpr]) (Map.elems allModules)
    in ExprRoot allExprs