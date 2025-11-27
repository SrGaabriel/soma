module Ide.Project.Resolve (
    ModuleResolver,
    newResolver,
    newResolverFromMetadata,
    resolveModule,
    resolveModuleToPath,
    resolvePathToModule,
    listAllModules,
    listProjectModules,
    ResolvedModule (..),
    getProjectRoot,
    getProjectName,
) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)

data ResolvedModule = ResolvedModule
    { rmModuleName :: !Text
    , rmPackageName :: !Text
    , rmFilePath :: !FilePath
    , rmIsLocal :: !Bool
    }
    deriving (Eq, Show)

data ModuleResolver = ModuleResolver
    { mrProjectRoot :: !FilePath
    , mrProjectName :: !Text
    , mrModulesByName :: !(Map Text ResolvedModule)
    , mrModulesByPath :: !(Map FilePath ResolvedModule)
    }
    deriving (Show)

newResolverFromMetadata ::
    FilePath ->
    Text ->
    [(Text, Bool)] ->
    [(Text, FilePath, Text)] ->
    ModuleResolver
newResolverFromMetadata projectRoot rootPackage packages modules =
    let packageIsRoot = Map.fromList packages
        resolvedModules =
            [ ResolvedModule
                { rmModuleName = modName
                , rmPackageName = pkgName
                , rmFilePath = path
                , rmIsLocal = Map.findWithDefault False pkgName packageIsRoot
                }
            | (modName, path, pkgName) <- modules
            ]
        byName = Map.fromList [(rmModuleName m, m) | m <- resolvedModules]
        byPath = Map.fromList [(rmFilePath m, m) | m <- resolvedModules]
    in ModuleResolver
        { mrProjectRoot = projectRoot
        , mrProjectName = rootPackage
        , mrModulesByName = byName
        , mrModulesByPath = byPath
        }

newResolver :: FilePath -> Text -> ModuleResolver
newResolver projectRoot projectName =
    ModuleResolver
        { mrProjectRoot = projectRoot
        , mrProjectName = projectName
        , mrModulesByName = Map.empty
        , mrModulesByPath = Map.empty
        }

resolveModule :: ModuleResolver -> Text -> Maybe ResolvedModule
resolveModule resolver moduleName = Map.lookup moduleName (mrModulesByName resolver)

resolveModuleToPath :: ModuleResolver -> Text -> Maybe FilePath
resolveModuleToPath resolver moduleName = rmFilePath <$> resolveModule resolver moduleName

resolvePathToModule :: ModuleResolver -> FilePath -> Maybe ResolvedModule
resolvePathToModule resolver filePath = Map.lookup filePath (mrModulesByPath resolver)

listAllModules :: ModuleResolver -> [ResolvedModule]
listAllModules = Map.elems . mrModulesByName

listProjectModules :: ModuleResolver -> [ResolvedModule]
listProjectModules resolver = filter rmIsLocal $ Map.elems (mrModulesByName resolver)

getProjectRoot :: ModuleResolver -> FilePath
getProjectRoot = mrProjectRoot

getProjectName :: ModuleResolver -> Text
getProjectName = mrProjectName
