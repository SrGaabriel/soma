module Project.Check (
    CheckedModule (..),
    checkModule,
    checkModulesInOrder,
) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Inference.Assembler (MetalTypeEnv, inferModule)
import Inference.Core (InstanceEnv)
import Inference.Errors (InferenceError)
import Inference.Resolver (runResolverWithEnv)
import Metal.Expr (TypedExpr)
import Metal.Gen.Metadata (extractConstructorMetadata)
import Metal.Lower (LowerResult (..), lowerModule, runLower)
import Metal.Metadata (MetallicConstructorMetadata)
import Project.Extracts (extractSymbolImports, resolveImport)
import Project.Module (ModuleInfo (..), ModuleName)
import Project.Symbols (Symbol (..))
import Syntax.Tree (Expr)
import Typing.Types (Constraint, QualifiedType (..), TyVar, Type)

data CheckedModule = CheckedModule
    { checkedModuleName :: ModuleName
    , checkedResolvedAst :: Expr
    , checkedLowerResult :: LowerResult
    , checkedTypedBindings :: [(String, TypedExpr, [Type], Type, [TyVar], [Constraint], Bool)]
    , checkedPublicSymbols :: Map Symbol QualifiedType
    , checkedInstances :: InstanceEnv
    }
    deriving (Show)

checkModule ::
    String ->
    ModuleInfo ->
    Map ModuleName CheckedModule ->
    Map String (Map Symbol QualifiedType) ->
    Map String InstanceEnv ->
    Map String MetallicConstructorMetadata ->
    ([InferenceError], CheckedModule)
checkModule packageName modInfo checkedDeps externalDeps externalInstances externalConstructors =
    let modName = moduleName modInfo
        ast = moduleAst modInfo

        -- Resolve imports
        imports = extractSymbolImports ast
        checked = Map.map (\c -> (checkedPublicSymbols c, checkedInstances c)) checkedDeps
        resolve = resolveImport checked externalDeps externalInstances
        importsResolved = map resolve imports
        seedEnv = Map.unions $ map fst importsResolved
        seedInstances = Map.unions $ map snd importsResolved

        -- Run resolver to get resolved AST and type environment
        (resolverErrors, (resolvedAst, fullEnv, instanceEnv)) =
            runResolverWithEnv packageName modName seedEnv seedInstances ast

        -- Extract constructor metadata for lowering (merge local and external)
        localConstructorMeta = extractConstructorMetadata resolvedAst
        constructorMeta = Map.union localConstructorMeta externalConstructors

        -- Lower resolved AST to Metal IR
        lowerResult = runLower constructorMeta (lowerModule resolvedAst)

        -- Build Metal type environment from Symbol-keyed environment
        metalTypeEnv = symbolEnvToMetalEnv fullEnv

        -- Run Metal-based type inference
        (inferenceErrors, typedBindings) =
            inferModule packageName modName metalTypeEnv instanceEnv lowerResult

        -- Extract new definitions (public symbols)
        newDefs = Map.difference fullEnv seedEnv

        allErrors = resolverErrors ++ inferenceErrors

        checkedModule =
            CheckedModule
                { checkedModuleName = modName
                , checkedResolvedAst = resolvedAst
                , checkedLowerResult = lowerResult
                , checkedTypedBindings = typedBindings
                , checkedPublicSymbols = newDefs
                , checkedInstances = instanceEnv
                }
    in (allErrors, checkedModule)

-- | Convert Symbol-keyed type environment to String-keyed Metal environment
symbolEnvToMetalEnv :: Map Symbol QualifiedType -> MetalTypeEnv
symbolEnvToMetalEnv symEnv =
    Map.fromList
        [ (resolvedSymbolName sym, qty)
        | (sym, qty) <- Map.toList symEnv
        ]

checkModulesInOrder ::
    [ModuleName] ->
    Map ModuleName ModuleInfo ->
    Map String (Map Symbol QualifiedType) ->
    Map String InstanceEnv ->
    Map String MetallicConstructorMetadata ->
    String ->
    ([(ModuleName, [InferenceError])], Map ModuleName CheckedModule)
checkModulesInOrder sorted graph externalDeps externalInstances externalConstructors packageName =
    go sorted Map.empty []
  where
    go [] checked errors = (errors, checked)
    go (modName : rest) checked errors =
        case Map.lookup modName graph of
            Nothing -> go rest checked errors
            Just modInfo ->
                let (modErrors, checkedMod) = checkModule packageName modInfo checked externalDeps externalInstances externalConstructors
                    newChecked = Map.insert modName checkedMod checked
                    newErrors = if null modErrors then errors else errors ++ [(modName, modErrors)]
                in go rest newChecked newErrors
