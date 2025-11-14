{-# LANGUAGE RecordWildCards #-}

module Incremental where

import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import System.FilePath
import Project.Symbols
import Project.Graph
import Typing.Types
import Syntax.Tree
import Inference.Core
import Language.LSP.Protocol.Types

-- Incremental compilation state for workspace
data WorkspaceState = WorkspaceState
    { wsModules :: Map.Map FilePath ModuleState
    , wsDependencyGraph :: Map.Map FilePath [FilePath]
    , wsModuleGraph :: ModuleGraph
    }

data ModuleAnalysis = ModuleAnalysis
    { maAst :: Maybe Expr
    , maTypeMap :: Maybe TypeMap
    , maSymbolEnv :: Maybe (Map.Map Symbol QualifiedType)
    , maDiagnostics :: [Diagnostic]
    , maParseError :: Maybe String
    }

data ModuleState = ModuleState
    { msAnalysis :: ModuleAnalysis
    , msImports :: [(String, [String])]  -- Module imports
    , msLastModified :: Maybe Integer
    , msNeedsRecompile :: Bool
    }

-- Build initial workspace state
buildWorkspaceState :: FilePath -> IO WorkspaceState
buildWorkspaceState rootPath = do
    -- Discover all .soma files
    modules <- findModules "workspace" rootPath
    
    -- Parse all modules to extract imports
    moduleStates <- mapM analyzeInitial modules
    
    let modulesMap = Map.fromList moduleStates
        depGraph = buildDepGraphFromStates modulesMap
    
    return $ WorkspaceState modulesMap depGraph Map.empty
  where
    analyzeInitial :: (String, FilePath) -> IO (FilePath, ModuleState)
    analyzeInitial (name, path) = do
        content <- readFile path
        parseResult <- parseModuleFromString name content
        
        let imports = case parseResult of
                Right modInfo -> extractSymbolImports (moduleAst modInfo)
                Left _ -> []
        
        return (path, ModuleState emptyAnalysis imports Nothing True)

-- Update a single file and determine what needs recompilation
updateFile :: FilePath -> String -> WorkspaceState -> IO WorkspaceState
updateFile filePath content ws@WorkspaceState{..} = do
    -- Parse and analyze the file
    let moduleName = dropExtension (takeFileName filePath)
    parseResult <- parseModuleFromString moduleName content
    
    case parseResult of
        Left _ -> return ws  -- Keep old state on parse error
        Right modInfo -> do
            let ast = moduleAst modInfo
                imports = extractSymbolImports ast
            
            -- Check if imports changed (affects dependency graph)
            let oldImports = maybe [] msImports (Map.lookup filePath wsModules)
                importsChanged = oldImports /= imports
            
            -- Rebuild dependency graph if needed
            let newDepGraph = if importsChanged
                    then rebuildDepGraph filePath imports wsDependencyGraph
                    else wsDependencyGraph
            
            -- Mark dependents for recompilation
            let affectedFiles = if importsChanged
                    then findTransitiveDependents filePath newDepGraph
                    else findDirectDependents filePath newDepGraph
            
            -- Perform analysis with proper dependencies
            analysis <- analyzeModuleWithDeps filePath content ws
            
            let newState = ModuleState analysis imports Nothing False
                newModules = Map.insert filePath newState $
                    markForRecompile affectedFiles wsModules
            
            return $ WorkspaceState newModules newDepGraph wsModuleGraph

-- Analyze module with dependency information
analyzeModuleWithDeps :: FilePath -> String -> WorkspaceState -> IO ModuleAnalysis
analyzeModuleWithDeps filePath content WorkspaceState{..} = do
    let moduleName = dropExtension (takeFileName filePath)
    parseResult <- parseModuleFromString moduleName content
    
    case parseResult of
        Left parseErr -> do
            let diag = parseErrorToDiagnostic parseErr
            return $ emptyAnalysis { maParseError = Just parseErr, maDiagnostics = [diag] }
        
        Right modInfo -> do
            let ast = moduleAst modInfo
                imports = extractSymbolImports ast
            
            -- Build seed environment from dependencies
            let seedEnv = buildSeedEnv imports wsModules
            
            -- Resolution
            resolvedResult <- runResolverWithEnv "workspace" moduleName seedEnv ast
            
            case resolvedResult of
                Left resolveErr -> do
                    let diag = analysisErrorToDiagnostic resolveErr filePath content
                    return $ emptyAnalysis { maAst = Just ast, maDiagnostics = [diag] }
                
                Right (resolvedAst, fullEnv, _) -> do
                    -- Type inference
                    typesResult <- inferTreeT "workspace" moduleName fullEnv resolvedAst
                    
                    case typesResult of
                        Left typeErrs -> do
                            let diags = map (\e -> inferenceErrorToDiagnostic e filePath content) typeErrs
                            return $ ModuleAnalysis
                                (Just resolvedAst) Nothing (Just fullEnv) diags Nothing
                        
                        Right types ->
                            return $ ModuleAnalysis
                                (Just resolvedAst) (Just types) (Just fullEnv) [] Nothing

-- Build environment from imported modules
buildSeedEnv :: [(String, [String])] -> Map.Map FilePath ModuleState -> Map.Map Symbol QualifiedType
buildSeedEnv imports modulesMap =
    Map.unions $ mapMaybe buildFromImport imports
  where
    buildFromImport :: (String, [String]) -> Maybe (Map.Map Symbol QualifiedType)
    buildFromImport (impMod, symbols) = do
        -- Find the module in our workspace
        let matchingModule = Map.filter (\ms -> matchesImport impMod ms) modulesMap
        case Map.elems matchingModule of
            (ms:_) -> do
                env <- maSymbolEnv (msAnalysis ms)
                return $ filterSymbolsByNames symbols env
            [] -> Nothing
    
    matchesImport :: String -> ModuleState -> Bool
    matchesImport impName _ms = True  -- Implement proper matching

-- Dependency graph operations
buildDepGraphFromStates :: Map.Map FilePath ModuleState -> Map.Map FilePath [FilePath]
buildDepGraphFromStates states =
    Map.map extractDeps states
  where
    extractDeps :: ModuleState -> [FilePath]
    extractDeps ms = mapMaybe resolveImportToPath (msImports ms)
    
    resolveImportToPath :: (String, [String]) -> Maybe FilePath
    resolveImportToPath (modName, _) = 
        -- Find filepath for module name
        let matching = Map.filter (\ms -> moduleNameMatches modName ms) states
        in case Map.keys matching of
            (path:_) -> Just path
            [] -> Nothing
    
    moduleNameMatches :: String -> ModuleState -> Bool
    moduleNameMatches _name _ms = True  -- Implement

rebuildDepGraph :: FilePath -> [(String, [String])] -> Map.Map FilePath [FilePath] -> Map.Map FilePath [FilePath]
rebuildDepGraph filePath newImports oldGraph =
    let newDeps = mapMaybe (resolveImportPath filePath) newImports
    in Map.insert filePath newDeps oldGraph
  where
    resolveImportPath :: FilePath -> (String, [String]) -> Maybe FilePath
    resolveImportPath _ _ = Nothing  -- Implement

findDirectDependents :: FilePath -> Map.Map FilePath [FilePath] -> [FilePath]
findDirectDependents target depGraph =
    Map.keys $ Map.filter (elem target) depGraph

findTransitiveDependents :: FilePath -> Map.Map FilePath [FilePath] -> [FilePath]
findTransitiveDependents target depGraph =
    go [target] []
  where
    go [] acc = acc
    go (f:fs) acc =
        let deps = findDirectDependents f depGraph
            newDeps = filter (`notElem` acc) deps
        in go (fs ++ newDeps) (acc ++ newDeps)

markForRecompile :: [FilePath] -> Map.Map FilePath ModuleState -> Map.Map FilePath ModuleState
markForRecompile files modulesMap =
    foldr (\f -> Map.adjust (\ms -> ms { msNeedsRecompile = True }) f) modulesMap files

-- Parallel compilation
recompileAffected :: WorkspaceState -> IO WorkspaceState
recompileAffected ws@WorkspaceState{..} = do
    let needsRecompile = Map.filter msNeedsRecompile wsModules
        sorted = topologicalSort needsRecompile wsDependencyGraph
    
    -- Compile in dependency order
    foldM compileOne ws sorted
  where
    compileOne :: WorkspaceState -> FilePath -> IO WorkspaceState
    compileOne currentWs filePath = do
        content <- readFile filePath
        updateFile filePath content currentWs

topologicalSort :: Map.Map FilePath ModuleState -> Map.Map FilePath [FilePath] -> [FilePath]
topologicalSort modules depGraph =
    reverse $ go (Map.keys modules) []
  where
    go [] acc = acc
    go (f:fs) acc
        | f `elem` acc = go fs acc
        | otherwise =
            let deps = Map.findWithDefault [] f depGraph
                sortedDeps = go (filter (`Map.member` modules) deps) acc
            in go fs (f : sortedDeps)