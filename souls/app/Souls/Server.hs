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
    IO (Either [SomeError] LspCompiledModule)
compileModuleForLSP modName filePath content ast compiledDeps = do
    let imports = extractSymbolImports ast
        seedEnv = Map.unions $ map resolveImport imports

    resolvedResult <- runResolverWithEnv "lsp" modName seedEnv ast
    case resolvedResult of
        Left err -> do
            return $ Left [SomeError err filePath content "INFERENCE"]
        Right (resolvedAst, fullEnv, instanceEnv) -> do
            let typesResult = inferTree "lsp" modName fullEnv instanceEnv resolvedAst

            case typesResult of
                Left errs -> do
                    return $ Left $ map (\e -> SomeError e filePath content "INFERENCE") errs
                Right types -> do
                    let newDefs = Map.difference fullEnv seedEnv
                    return
                        $ Right
                        $ LspCompiledModule
                            { lcmModuleName = modName
                            , lcmResolvedAst = resolvedAst
                            , lcmTypeMap = types
                            , lcmFilePath = filePath
                            , lcmPublicSymbols = newDefs
                            , lcmSourceContent = T.pack content
                            }
  where
    resolveImport (impMod, syms) =
        case findModuleByName impMod compiledDeps of
            Just matchedModule ->
                filterSymbolsByNames syms (lcmPublicSymbols matchedModule)
            Nothing -> Map.empty

findModuleByName :: String -> Map.Map FilePath LspCompiledModule -> Maybe LspCompiledModule
findModuleByName name mods =
    listToMaybe [cm | cm <- Map.elems mods, lcmModuleName cm == name]
