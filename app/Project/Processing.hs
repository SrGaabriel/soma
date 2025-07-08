{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Project.Processing where

import qualified Data.Map as Map
import Inference.Resolver (runResolverWithEnv)
import Inference.Tree (analyzeTreeT)
import Logging.ErrorPrinter (printError)
import Logging.PrettyTrees (treeShowTypeMapL)
import Project.Graph (ModuleGraph)
import Project.Module (ModuleInfo (..))
import Project.Name (Name)
import Syntax.Tree (Expr (..), exprChildren)
import System.Directory.Internal.Prelude (exitFailure)

extractSymbolImports :: Expr -> [(Name, Maybe [String])]
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

processModules :: [Name] -> ModuleGraph -> IO ()
processModules sorted graph = go Map.empty sorted
  where
    go _modulesEnv [] = putStrLn "All modules processed"
    go modulesEnv (modName : rest) = do
        let Just modInfo = Map.lookup modName graph
            ast = moduleAst modInfo
        let imports = extractSymbolImports ast
            seedEnv =
                Map.unions
                    $ map
                        ( \(impMod, mSyms) ->
                            case Map.lookup impMod modulesEnv of
                                Just modEnv -> case mSyms of
                                    Just syms -> Map.filterWithKey (\k _ -> k `elem` syms) modEnv
                                    Nothing -> modEnv
                                Nothing -> Map.empty
                        )
                        imports
        resolvedResult <- runResolverWithEnv seedEnv ast
        (resolvedAst, fullEnv) <- case resolvedResult of
            Left err -> printError err (modulePath modInfo) (moduleContent modInfo) "ANALYSIS" >> exitFailure
            Right res -> return res
        let newDefs = Map.difference fullEnv seedEnv
        types <- case analyzeTreeT fullEnv resolvedAst of
            Left errs -> mapM_ (\e -> printError e (modulePath modInfo) (moduleContent modInfo) "INFERENCE") errs >> exitFailure
            Right t -> return t
        putStrLn $ "Module " ++ modName ++ " inferred types:\n" ++ treeShowTypeMapL ast types
        go (Map.insert modName newDefs modulesEnv) rest
