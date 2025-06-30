module Project.Graph where

import System.Directory (listDirectory, doesDirectoryExist)
import System.FilePath ((</>), takeExtension, dropExtension)
import qualified Data.Map as Map
import Project.Name (Name)
import Control.Concurrent.Async (mapConcurrently)
import Project.Module (ModuleInfo (moduleAst), moduleName, ModuleName)
import Project.Parsing (parseModule)
import Syntax.Tree (Expr(..), exprChildren)
import Data.Graph (SCC(AcyclicSCC, CyclicSCC), stronglyConnComp)
import Data.Either (partitionEithers)
import Parsing.Errors (ParsingError)

type ModuleGraph = Map.Map Name ModuleInfo

findModules :: FilePath -> IO [(Name, FilePath)]
findModules = go ""
  where
    go prefix dir = do
      entries <- listDirectory dir
      fmap concat $ mapM (handleEntry prefix dir) entries

    handleEntry prefix dir entry = do
      let fullPath = dir </> entry
      isDir <- doesDirectoryExist fullPath
      if isDir
        then go (extendMod prefix entry) fullPath
        else if takeExtension entry == ".soma"
          then return [(extendMod prefix (dropExtension entry), fullPath)]
          else return []

    extendMod "" part = part
    extendMod prefix part = prefix ++ "." ++ part

buildModuleGraph :: [(Name, FilePath)] -> IO (Either [ParsingError] ModuleGraph)
buildModuleGraph modules = do
  results <- mapConcurrently parseModule modules
  case partitionEithers results of
    ([], parsedModules) -> return $ Right $ Map.fromList [(moduleName modInfo, modInfo) | modInfo <- parsedModules]
    (errors, _) -> return $ Left errors

type DependencyGraph = Map.Map Name [Name]

buildDependencyGraph :: ModuleGraph -> DependencyGraph
buildDependencyGraph =
  Map.map extract . Map.map moduleAst
  where
    extract = extractImports

extractImports :: Expr -> [ModuleName]
extractImports expr = case expr of
    ExprImport name _ -> [takeWhile (/= ':') name]
    _ -> concatMap extractImports (exprChildren expr)

topoSortModules :: DependencyGraph -> Either [[ModuleName]] [ModuleName]
topoSortModules depGraph =
  let nodes = [ (m, m, deps) | (m, deps) <- Map.toList depGraph ]
      sccs = stronglyConnComp nodes
   in case partitionEithers (map toEither sccs) of
        ([], sorted) -> Right sorted
        (cycles, _) -> Left cycles
  where
    toEither (AcyclicSCC m) = Right m
    toEither (CyclicSCC ms) = Left ms