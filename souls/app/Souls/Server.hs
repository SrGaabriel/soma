{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE OverloadedStrings #-}

module Souls.Server (LspCompiledModule (..), LspState (..), compileModuleForLSP, findModuleByName) where

import Control.Concurrent.STM
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)
import qualified Data.Text as T
import Inference.Assembler (inferTree)
import Inference.Core (TypeMap)
import Inference.Resolver (runResolverWithEnv)
import Logging.Errors (SomeError (SomeError))
import Project.Extracts (extractSymbolImports, filterSymbolsByNames)
import Project.Graph
import Project.Symbols (Symbol)
import Syntax.Tree (Expr (..))
import Typing.Types (QualifiedType)

data LspCompiledModule = LspCompiledModule
    { lcmModuleName :: String
    , lcmFilePath :: FilePath
    , lcmResolvedAst :: Expr
    , lcmTypeMap :: TypeMap
    , lcmPublicSymbols :: Map.Map Symbol QualifiedType
    , lcmSourceContent :: T.Text
    }

data LspState = LspState
    { stateModules :: TVar (Map.Map FilePath LspCompiledModule)
    , stateWorkspaceRoot :: TVar (Maybe FilePath)
    , stateModuleGraph :: TVar (Maybe ModuleGraph)
    }

compileModuleForLSP ::
    String ->
    FilePath ->
    String ->
    Expr ->
    Map.Map FilePath LspCompiledModule ->
    ([SomeError], LspCompiledModule)
compileModuleForLSP modName filePath content ast compiledDeps = do
    let imports = extractSymbolImports ast
        seedEnv = Map.unions $ map resolveImport imports

    let (resolverErrors, (resolvedAst, fullEnv, instanceEnv)) = runResolverWithEnv "lsp" modName seedEnv ast
    let (inferenceErrors, types) = inferTree "lsp" modName fullEnv instanceEnv resolvedAst

    let allErrors = map (\e -> SomeError e filePath content "INFERENCE") (resolverErrors ++ inferenceErrors)
    let newDefs = Map.difference fullEnv seedEnv

    let compiledModule =
            LspCompiledModule
                { lcmModuleName = modName
                , lcmResolvedAst = resolvedAst
                , lcmTypeMap = types
                , lcmFilePath = filePath
                , lcmPublicSymbols = newDefs
                , lcmSourceContent = T.pack content
                }

    (allErrors, compiledModule)
  where
    resolveImport (impMod, syms) =
        case findModuleByName impMod compiledDeps of
            Just matchedModule ->
                filterSymbolsByNames syms (lcmPublicSymbols matchedModule)
            Nothing -> Map.empty

findModuleByName :: String -> Map.Map FilePath LspCompiledModule -> Maybe LspCompiledModule
findModuleByName name mods =
    listToMaybe [cm | cm <- Map.elems mods, lcmModuleName cm == name]
