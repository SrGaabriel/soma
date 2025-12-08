module Project.Graph where

import Control.Concurrent.Async (mapConcurrently)
import Data.Either (partitionEithers)
import Data.Graph (SCC (AcyclicSCC, CyclicSCC), stronglyConnComp)
import qualified Data.Map as Map
import Format.Errors (SomeError)
import Project.Module (ModuleInfo (..), ModuleName)
import Project.Parsing (injectPrelude, parseModule, preludeModuleName)
import Syntax.Tree (Expr (..), exprChildren)
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath (dropExtension, takeExtension, (</>))

type ModuleGraph = Map.Map String ModuleInfo

findModules :: String -> FilePath -> IO [(String, FilePath)]
findModules packageName = go ""
  where
    go prefix dir = do
        entries <- listDirectory dir
        concat <$> mapM (handleEntry prefix dir) entries

    handleEntry prefix dir entry = do
        let fullPath = dir </> entry
        isDir <- doesDirectoryExist fullPath
        if isDir
            then go (extendMod prefix entry) fullPath
            else
                if takeExtension entry == ".soma"
                    then return [(packageName ++ "/" ++ extendMod prefix (dropExtension entry), fullPath)]
                    else return []

    extendMod "" part = part
    extendMod prefix part = prefix ++ "/" ++ part

buildModuleGraph :: [(String, FilePath)] -> IO (Either [SomeError] ModuleGraph)
buildModuleGraph modules = do
    results <- mapConcurrently (uncurry parseModule) modules
    case partitionEithers results of
        ([], parsedModules) -> return $ Right $ Map.fromList [(moduleName modInfo, modInfo) | modInfo <- parsedModules]
        (errors, _) -> return $ Left $ concat errors

type DependencyGraph = Map.Map String [String]

buildDependencyGraph :: ModuleGraph -> DependencyGraph
buildDependencyGraph =
    Map.map extractImports . Map.map moduleAst

extractImports :: Expr -> [ModuleName]
extractImports expr = case expr of
    ExprImport name _ _ -> [name]
    _ -> concatMap extractImports (exprChildren expr)

topoSortModules :: DependencyGraph -> Either [[ModuleName]] [ModuleName]
topoSortModules depGraph =
    let nodes = [(m, m, deps) | (m, deps) <- Map.toList depGraph]
        sccs = stronglyConnComp nodes
    in case partitionEithers (map toEither sccs) of
        ([], sorted) -> Right sorted
        (cycles, _) -> Left cycles
  where
    toEither (AcyclicSCC m) = Right m
    toEither (CyclicSCC ms) = Left ms

{- | Inject prelude imports into all modules in the graph that should have it.
A module gets the prelude injected if it's not the prelude itself.
-}
injectPreludeIntoGraph :: [String] -> ModuleGraph -> ModuleGraph
injectPreludeIntoGraph preludeSymbols = Map.mapWithKey injectIfNeeded
  where
    injectIfNeeded modName modInfo
        | modName == preludeModuleName = modInfo -- Don't inject into prelude itself
        | otherwise = modInfo{moduleAst = injectPrelude preludeSymbols (moduleAst modInfo)}
