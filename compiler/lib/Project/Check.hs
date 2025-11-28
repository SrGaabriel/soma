module Project.Check (
    CheckedModule (..),
    checkModule,
    checkModulesInOrder,
) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Inference.Assembler (inferTree)
import Inference.Core (InstanceEnv, TypeMap)
import Inference.Errors (InferenceError)
import Inference.Resolver (runResolverWithEnv)
import Project.Extracts (extractSymbolImports, resolveImport)
import Project.Module (ModuleInfo (..), ModuleName)
import Project.Symbols (Symbol)
import Syntax.Tree (Expr)
import Typing.Types (QualifiedType)

data CheckedModule = CheckedModule
    { checkedModuleName :: ModuleName
    , checkedResolvedAst :: Expr
    , checkedTypeMap :: TypeMap
    , checkedPublicSymbols :: Map Symbol QualifiedType
    , checkedInstances :: InstanceEnv
    }
    deriving (Show)

checkModule ::
    String -> -- Package name
    ModuleInfo -> -- Module to check
    Map ModuleName CheckedModule -> -- Already checked local modules
    Map String (Map Symbol QualifiedType) -> -- External dependency types
    Map String InstanceEnv -> -- External dependency instances
    ([InferenceError], CheckedModule)
checkModule packageName modInfo checkedDeps externalDeps externalInstances =
    let modName = moduleName modInfo
        ast = moduleAst modInfo

        imports = extractSymbolImports ast
        checked = Map.map (\c -> (checkedPublicSymbols c, checkedInstances c)) checkedDeps
        resolve = resolveImport checked externalDeps externalInstances
        importsResolved = map resolve imports
        seedEnv = Map.unions $ map fst importsResolved
        seedInstances = Map.unions $ map snd importsResolved

        (resolverErrors, (resolvedAst, fullEnv, instanceEnv)) =
            runResolverWithEnv packageName modName seedEnv seedInstances ast

        (inferenceErrors, types) = inferTree packageName modName fullEnv instanceEnv resolvedAst

        newDefs = Map.difference fullEnv seedEnv

        allErrors = resolverErrors ++ inferenceErrors

        checkedModule =
            CheckedModule
                { checkedModuleName = modName
                , checkedResolvedAst = resolvedAst
                , checkedTypeMap = types
                , checkedPublicSymbols = newDefs
                , checkedInstances = instanceEnv
                }
    in (allErrors, checkedModule)

checkModulesInOrder ::
    [ModuleName] -> -- Sorted module names
    Map ModuleName ModuleInfo -> -- Module graph
    Map String (Map Symbol QualifiedType) -> -- External dependency types
    Map String InstanceEnv -> -- External dependency instances
    String -> -- Package name
    ([(ModuleName, [InferenceError])], Map ModuleName CheckedModule)
checkModulesInOrder sorted graph externalDeps externalInstances packageName =
    go sorted Map.empty []
  where
    go [] checked errors = (errors, checked)
    go (modName : rest) checked errors =
        case Map.lookup modName graph of
            Nothing -> go rest checked errors
            Just modInfo ->
                let (modErrors, checkedMod) = checkModule packageName modInfo checked externalDeps externalInstances
                    newChecked = Map.insert modName checkedMod checked
                    newErrors = if null modErrors then errors else errors ++ [(modName, modErrors)]
                in go rest newChecked newErrors
