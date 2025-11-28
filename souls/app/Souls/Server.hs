{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE OverloadedStrings #-}

module Souls.Server (LspCompiledModule (..), LspState (..), compileModuleForLSP, findModuleByName) where

import Control.Concurrent.STM
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)
import qualified Data.Text as T
import Format.Errors (SomeError (SomeError))
import Inference.Assembler (inferTree)
import Inference.Core (InstanceEnv, TypeEnv, TypeMap)
import Inference.Resolver (runResolverWithEnv)
import Language.LSP.Protocol.Types (Uri)
import Project.Extracts (
    extractSymbolImports,
    resolveImport,
 )
import Project.Graph
import Souls.Haoma (ExternalDeps (..), HaomaProjectCache)
import Syntax.Tree (Expr (..))

data LspCompiledModule = LspCompiledModule
    { lcmModuleName :: String
    , lcmFilePath :: FilePath
    , lcmResolvedAst :: Expr
    , lcmTypeMap :: TypeMap
    , lcmPublicSymbols :: TypeEnv
    , lcmInstances :: InstanceEnv
    , lcmSourceContent :: T.Text
    }

data LspState = LspState
    { stateModules :: TVar (Map.Map FilePath LspCompiledModule)
    , stateWorkspaceRoot :: TVar (Maybe FilePath)
    , stateModuleGraph :: TVar (Maybe ModuleGraph)
    , stateHaomaProjects :: TVar (Map.Map FilePath HaomaProjectCache)
    , stateFileToProject :: TVar (Map.Map FilePath FilePath)
    , stateOpenFiles :: TVar (Map.Map FilePath Uri)
    }

compileModuleForLSP ::
    String ->
    FilePath ->
    String ->
    Expr ->
    Map.Map FilePath LspCompiledModule ->
    ExternalDeps ->
    ([SomeError], LspCompiledModule)
compileModuleForLSP modName filePath content ast compiledDeps externalDeps =
    let imports = extractSymbolImports ast
        compiledByName = Map.fromList [(lcmModuleName c, (lcmPublicSymbols c, lcmInstances c)) | c <- Map.elems compiledDeps]
        resolve = resolveImport compiledByName (edTypes externalDeps) (edInstances externalDeps)
        importsResolved = map resolve imports
        seedEnv = Map.unions $ map fst importsResolved
        seedInstances = Map.unions $ map snd importsResolved
        (resolverErrors, (resolvedAst, fullEnv, instanceEnv)) =
            runResolverWithEnv
                "lsp"
                modName
                seedEnv
                seedInstances
                ast
        (inferenceErrors, types) = inferTree "lsp" modName fullEnv instanceEnv resolvedAst

        allErrors = map (\e -> SomeError e filePath content "INFERENCE") (resolverErrors ++ inferenceErrors)
        newDefs = Map.difference fullEnv seedEnv

        compiledModule =
            LspCompiledModule
                { lcmModuleName = modName
                , lcmResolvedAst = resolvedAst
                , lcmTypeMap = types
                , lcmFilePath = filePath
                , lcmPublicSymbols = newDefs
                , lcmInstances = instanceEnv
                , lcmSourceContent = T.pack content
                }
    in (allErrors, compiledModule)

findModuleByName :: String -> Map.Map FilePath LspCompiledModule -> Maybe LspCompiledModule
findModuleByName name mods =
    listToMaybe [cm | cm <- Map.elems mods, lcmModuleName cm == name]
