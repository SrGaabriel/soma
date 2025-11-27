{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Souls.Haoma (
    HaomaProject (..),
    HaomaCheckOutput (..),
    HaomaModuleOutput (..),
    HaomaDiagnostic (..),
    HaomaPosition (..),
    HaomaRange (..),
    HaomaMetadata (..),
    HaomaPackageInfo (..),
    HaomaModuleInfo (..),
    findHaomaProject,
    isHaomaProject,
    runHaomaCheck,
    runHaomaMetadata,
    haomaCheckFile,
    loadExternalDeps,
) where

import Control.Exception (try)
import Data.Aeson (FromJSON (..), eitherDecode, withObject, (.:), (.:?))
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import GHC.Generics (Generic)
import Inference.Core (InstanceEnv, TypeEnv)
import Inference.Resolver (runResolverWithEnv)
import Lexing.Lexer (lexCode)
import Parsing.Ast (parse)
import Project.Extracts (extractSymbolImports, resolveImport)
import Project.Graph (extractImports, topoSortModules)
import Syntax.Tree (Expr)
import System.Directory (doesFileExist)
import System.Exit (ExitCode (..))
import System.FilePath (takeDirectory, (</>))
import System.Process (readProcessWithExitCode)

data HaomaProject = HaomaProject
    { hpRoot :: FilePath
    , hpName :: String
    }
    deriving (Show, Eq)

data HaomaPosition = HaomaPosition
    { hpLine :: !Int
    , hpCharacter :: !Int
    }
    deriving (Show, Eq, Generic)

instance FromJSON HaomaPosition where
    parseJSON = withObject "HaomaPosition" $ \v ->
        HaomaPosition
            <$> v .: "line"
            <*> v .: "character"

data HaomaRange = HaomaRange
    { hrStart :: !HaomaPosition
    , hrEnd :: !HaomaPosition
    }
    deriving (Show, Eq, Generic)

instance FromJSON HaomaRange where
    parseJSON = withObject "HaomaRange" $ \v ->
        HaomaRange
            <$> v .: "start"
            <*> v .: "end"

data HaomaDiagnostic = HaomaDiagnostic
    { hdFile :: !T.Text
    , hdRange :: !HaomaRange
    , hdSeverity :: !Int
    , hdMessage :: !T.Text
    , hdSource :: !T.Text
    , hdCode :: !(Maybe T.Text)
    }
    deriving (Show, Eq, Generic)

instance FromJSON HaomaDiagnostic where
    parseJSON = withObject "HaomaDiagnostic" $ \v ->
        HaomaDiagnostic
            <$> v .: "file"
            <*> v .: "range"
            <*> v .: "severity"
            <*> v .: "message"
            <*> v .: "source"
            <*> v .: "code"

data HaomaModuleOutput = HaomaModuleOutput
    { hmoSuccess :: !Bool
    , hmoDiagnostics :: ![HaomaDiagnostic]
    , hmoModuleName :: !(Maybe T.Text)
    }
    deriving (Show, Eq, Generic)

instance FromJSON HaomaModuleOutput where
    parseJSON = withObject "HaomaModuleOutput" $ \v ->
        HaomaModuleOutput
            <$> v .: "success"
            <*> v .: "diagnostics"
            <*> v .: "module"

data HaomaCheckOutput = HaomaCheckOutput
    { hcoSuccess :: !Bool
    , hcoModules :: ![HaomaModuleOutput]
    }
    deriving (Show, Eq, Generic)

instance FromJSON HaomaCheckOutput where
    parseJSON = withObject "HaomaCheckOutput" $ \v ->
        HaomaCheckOutput
            <$> v .: "success"
            <*> v .: "modules"

data HaomaModuleInfo = HaomaModuleInfo
    { hmiName :: !T.Text
    , hmiPath :: !FilePath
    , hmiPackage :: !T.Text
    }
    deriving (Show, Eq, Generic)

instance FromJSON HaomaModuleInfo where
    parseJSON = withObject "HaomaModuleInfo" $ \v ->
        HaomaModuleInfo
            <$> v .: "name"
            <*> v .: "path"
            <*> v .: "package"

data HaomaPackageInfo = HaomaPackageInfo
    { hpiName :: !T.Text
    , hpiRoot :: !FilePath
    , hpiVersion :: !T.Text
    , hpiIsRoot :: !Bool
    , hpiDependencies :: ![T.Text]
    }
    deriving (Show, Eq, Generic)

instance FromJSON HaomaPackageInfo where
    parseJSON = withObject "HaomaPackageInfo" $ \v ->
        HaomaPackageInfo
            <$> v .: "name"
            <*> v .: "root"
            <*> v .: "version"
            <*> v .: "is_root"
            <*> v .: "dependencies"

data HaomaMetadata = HaomaMetadata
    { hmSuccess :: !Bool
    , hmError :: !(Maybe T.Text)
    , hmRootPackage :: !T.Text
    , hmPackages :: ![HaomaPackageInfo]
    , hmModules :: ![HaomaModuleInfo]
    }
    deriving (Show, Eq, Generic)

instance FromJSON HaomaMetadata where
    parseJSON = withObject "HaomaMetadata" $ \v ->
        HaomaMetadata
            <$> v .: "success"
            <*> v .:? "error"
            <*> v .: "root_package"
            <*> v .: "packages"
            <*> v .: "modules"

haomaManifestName :: FilePath
haomaManifestName = "haoma.toml"

isHaomaProject :: FilePath -> IO Bool
isHaomaProject dir = doesFileExist (dir </> haomaManifestName)

findHaomaProject :: FilePath -> IO (Maybe HaomaProject)
findHaomaProject filePath = do
    let dir = takeDirectory filePath
    findProjectRoot dir
  where
    findProjectRoot :: FilePath -> IO (Maybe HaomaProject)
    findProjectRoot dir = do
        let manifestPath = dir </> haomaManifestName
        exists <- doesFileExist manifestPath
        if exists
            then do
                let name = takeDirectory dir
                return $ Just HaomaProject{hpRoot = dir, hpName = name}
            else
                let parent = takeDirectory dir
                in if parent == dir
                    then return Nothing
                    else findProjectRoot parent

runHaomaCheck :: HaomaProject -> IO (Either String HaomaCheckOutput)
runHaomaCheck HaomaProject{..} = do
    result <- try $ readProcessWithExitCode "haoma" ["check", "-p", hpRoot] ""
    case result of
        Left err -> return $ Left $ "Failed to run haoma: " ++ show (err :: IOError)
        Right (exitCode, stdout, _stderr) -> do
            case exitCode of
                ExitSuccess -> parseOutput stdout
                ExitFailure _ -> parseOutput stdout -- haoma check returns non-zero on errors
  where
    parseOutput :: String -> IO (Either String HaomaCheckOutput)
    parseOutput stdout = do
        let jsonLine = listToMaybe [line | line <- lines stdout, take 1 line == "{"]
        case jsonLine of
            Nothing -> return $ Left $ "No JSON output from haoma: " ++ stdout
            Just json -> return $ eitherDecode (BL.fromStrict $ encodeUtf8 json)

    encodeUtf8 :: String -> BS.ByteString
    encodeUtf8 = TE.encodeUtf8 . T.pack

runHaomaMetadata :: HaomaProject -> IO (Either String HaomaMetadata)
runHaomaMetadata HaomaProject{..} = do
    result <- try $ readProcessWithExitCode "haoma" ["metadata", "-p", hpRoot] ""
    case result of
        Left err -> return $ Left $ "Failed to run haoma: " ++ show (err :: IOError)
        Right (_exitCode, stdout, _stderr) -> parseOutput stdout
  where
    parseOutput :: String -> IO (Either String HaomaMetadata)
    parseOutput stdout = do
        let jsonLine = listToMaybe [line | line <- lines stdout, take 1 line == "{"]
        case jsonLine of
            Nothing -> return $ Left $ "No JSON output from haoma metadata: " ++ stdout
            Just json -> return $ eitherDecode (BL.fromStrict $ encodeUtf8 json)

    encodeUtf8 :: String -> BS.ByteString
    encodeUtf8 = TE.encodeUtf8 . T.pack

haomaCheckFile :: FilePath -> IO (Maybe (Either String HaomaCheckOutput))
haomaCheckFile filePath = do
    mProject <- findHaomaProject filePath
    case mProject of
        Nothing -> return Nothing
        Just project -> Just <$> runHaomaCheck project

loadExternalDeps ::
    HaomaProject ->
    IO (Either String (Map.Map String TypeEnv, Map.Map String InstanceEnv))
loadExternalDeps project = do
    metadataResult <- runHaomaMetadata project
    case metadataResult of
        Left err -> return $ Left err
        Right metadata -> do
            let rootPkg = T.unpack (hmRootPackage metadata)
                externalPkgs = [hpiName p | p <- hmPackages metadata, not (hpiIsRoot p)]
                externalModules =
                    [ (T.unpack (hmiPackage m), T.unpack (hmiName m), hmiPath m)
                    | m <- hmModules metadata
                    , hmiPackage m `elem` externalPkgs
                    ]

            compileExternalModules rootPkg externalModules

compileExternalModules ::
    String ->
    [(String, String, FilePath)] -> -- (package, module name, file path)
    IO (Either String (Map.Map String TypeEnv, Map.Map String InstanceEnv))
compileExternalModules _rootPkg modules = do
    parsedModules <- parseAllModules modules
    let moduleMap = Map.fromList [(modName, (pkgName, filePath, ast)) | (pkgName, modName, filePath, ast) <- parsedModules]
        depGraph = Map.fromList [(modName, extractImports ast) | (_, modName, _, ast) <- parsedModules]

    case topoSortModules depGraph of
        Left _cycles ->
            compileInOrder modules
        Right sorted -> do
            let sortedModules = [(pkgName, modName, filePath, ast) | modName <- sorted, Just (pkgName, filePath, ast) <- [Map.lookup modName moduleMap]]
            results <- compileModulesAccum Map.empty Map.empty sortedModules
            return $ Right results
  where
    parseAllModules :: [(String, String, FilePath)] -> IO [(String, String, FilePath, Expr)]
    parseAllModules [] = return []
    parseAllModules ((pkgName, modName, filePath) : rest) = do
        contentResult <- try $ readFile filePath
        case contentResult of
            Left (_ :: IOError) -> parseAllModules rest
            Right content -> do
                let contentText = T.pack content
                    (tokens, _) = lexCode contentText
                case parse tokens of
                    Left _ -> parseAllModules rest
                    Right (_, ast) -> do
                        restParsed <- parseAllModules rest
                        return $ (pkgName, modName, filePath, ast) : restParsed

    compileInOrder :: [(String, String, FilePath)] -> IO (Either String (Map.Map String TypeEnv, Map.Map String InstanceEnv))
    compileInOrder mods = do
        parsedMods <- parseAllModules mods
        results <- compileModulesAccum Map.empty Map.empty parsedMods
        return $ Right results

    compileModulesAccum ::
        Map.Map String TypeEnv ->
        Map.Map String InstanceEnv ->
        [(String, String, FilePath, Expr)] ->
        IO (Map.Map String TypeEnv, Map.Map String InstanceEnv)
    compileModulesAccum types instances [] = return (types, instances)
    compileModulesAccum types instances ((pkgName, modName, _filePath, ast) : rest) = do
        result <- compileExternalModuleAst pkgName modName ast types instances
        case result of
            Nothing ->
                compileModulesAccum types instances rest
            Just (newTypes, newInstances) -> do
                let types' = Map.insertWith Map.union pkgName newTypes types
                    instances' = Map.insertWith Map.union pkgName newInstances instances
                compileModulesAccum types' instances' rest

compileExternalModuleAst ::
    String ->
    String ->
    Expr ->
    Map.Map String TypeEnv ->
    Map.Map String InstanceEnv ->
    IO (Maybe (TypeEnv, InstanceEnv))
compileExternalModuleAst pkgName modName ast existingTypes existingInstances = do
    let imports = extractSymbolImports ast
        resolve = resolveImport Map.empty existingTypes existingInstances
        importsResolved = map resolve imports
        seedEnv = Map.unions $ map fst importsResolved
        seedInstances = Map.unions $ map snd importsResolved

    let (resolverErrors, (_, fullEnv, instanceEnv)) =
            runResolverWithEnv pkgName modName seedEnv seedInstances ast

    if not (null resolverErrors)
        then return Nothing
        else do
            let newDefs = Map.difference fullEnv seedEnv
            return $ Just (newDefs, instanceEnv)
