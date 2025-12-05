{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE OverloadedStrings #-}

module Souls.Server (LspCompiledModule (..), LspState (..), compileModuleForLSP, findModuleByName) where

import Control.Concurrent.STM
import Data.Int (Int32)
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)
import qualified Data.Text as T
import Format.Errors (SomeError (SomeError))
import Inference.Core (InstanceEnv, TypedBinding)
import Language.LSP.Protocol.Types (Uri)
import Metal.Lower (lowerModule, runLower)
import Project.Check (CheckedModule (..), checkModule)
import Project.Graph
import Project.Module (ModuleInfo (..))
import Project.Symbols (Symbol (..))
import Souls.Haoma (ExternalDeps (..), HaomaProjectCache)
import Syntax.Tree (Expr (..))
import Typing.Types (QualifiedType)

data LspCompiledModule = LspCompiledModule
    { lcmModuleName :: String
    , lcmFilePath :: FilePath
    , lcmResolvedAst :: Expr
    , lcmTypedBindings :: [TypedBinding]
    , lcmPublicSymbols :: Map.Map Symbol QualifiedType
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
    , stateFileVersions :: TVar (Map.Map FilePath Int32)
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
    let
        -- todo: review this, currently tokens are not needed by checkModule, so I'm passing empty list
        modInfo = ModuleInfo modName filePath content [] ast
        checkedByName = Map.fromList [(lcmModuleName c, toCheckedModule c) | c <- Map.elems compiledDeps]

        (inferenceErrors, checked) =
            checkModule
                "lsp"
                modInfo
                checkedByName
                (edTypes externalDeps)
                (edInstances externalDeps)
                Map.empty -- constructor metadata extracted internally by checkModule
        allErrors = map (\e -> SomeError e filePath content "INFERENCE") inferenceErrors

        compiledModule =
            LspCompiledModule
                { lcmModuleName = modName
                , lcmResolvedAst = checkedResolvedAst checked
                , lcmTypedBindings = checkedTypedBindings checked
                , lcmFilePath = filePath
                , lcmPublicSymbols = checkedPublicSymbols checked
                , lcmInstances = checkedInstances checked
                , lcmSourceContent = T.pack content
                }
    in
        (allErrors, compiledModule)

toCheckedModule :: LspCompiledModule -> CheckedModule
toCheckedModule cm =
    let lowerResult = runLower Map.empty (lowerModule (lcmResolvedAst cm))
    in CheckedModule
        { checkedModuleName = lcmModuleName cm
        , checkedResolvedAst = lcmResolvedAst cm
        , checkedLowerResult = lowerResult
        , checkedTypedBindings = lcmTypedBindings cm
        , checkedPublicSymbols = lcmPublicSymbols cm
        , checkedInstances = lcmInstances cm
        }

findModuleByName :: String -> Map.Map FilePath LspCompiledModule -> Maybe LspCompiledModule
findModuleByName name mods =
    listToMaybe [cm | cm <- Map.elems mods, lcmModuleName cm == name]
