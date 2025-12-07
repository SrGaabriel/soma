{-# LANGUAGE NamedFieldPuns #-}

module Metal.Gen.Entry (
    compileMetalModule,
    TypedLowerResult (
        TypedLowerResult,
        tlrBindings,
        tlrTypes,
        tlrInstances,
        tlrTypeClasses
    ),
) where

import qualified Data.Map as Map
import Inference.Core (TypedBinding, TypedInstanceMethod)
import Metal.Function (MetallicFunction (..))
import Metal.Metadata (MetallicConstructorMetadata, MetallicFunctionMetadata (MetallicFunctionMetadata), MetallicTypeClassMetadata, defaultFunctionAttributes)
import Metal.Module (MetallicInstance (..), MetallicModule (..), MetallicTypeDef)
import Project.Name (Name (..), LocalId (..), LocalPrefix (..), SyntheticId (..), SyntheticKind (..))
import Project.Unique (Unique (..))
import Typing.Types (QualifiedType (..), TyConstructor (..), TyUnique (..), Type (..), tyUniqueName)

data TypedLowerResult = TypedLowerResult
    { tlrBindings :: [TypedBinding]
    , tlrTypes :: [MetallicTypeDef]
    , tlrInstances :: [(QualifiedType, [TypedInstanceMethod])]
    , tlrTypeClasses :: [MetallicTypeClassMetadata]
    }
    deriving (Show)

compileMetalModule ::
    String ->
    TypedLowerResult ->
    Map.Map Name MetallicConstructorMetadata ->
    MetallicModule
compileMetalModule name TypedLowerResult{tlrBindings, tlrTypes, tlrInstances, tlrTypeClasses} _externalConstructors =
    let
        functions = map bindingToFunction tlrBindings

        instances = concatMap instanceToMetallicInstance tlrInstances
    in
        MetallicModule
            { mmName = name
            , mmFunctions = functions
            , mmTypes = tlrTypes
            , mmInstances = instances
            , mmTypeClasses = tlrTypeClasses
            }

bindingToFunction ::
    TypedBinding ->
    MetallicFunction
bindingToFunction (name, body, paramTypes, returnType, typeVars, constraints, attrs) =
    let params = zipWith (\i t -> (NLocal (LocalId LPParam i), t)) [0 :: Int ..] paramTypes
        metadata = MetallicFunctionMetadata typeVars constraints Nothing Nothing attrs
    in MetallicFunction name params returnType body metadata

instanceToMetallicInstance ::
    (QualifiedType, [TypedInstanceMethod]) ->
    [MetallicInstance]
instanceToMetallicInstance (qualType, methods) =
    let Forall _ _ constraintType = qualType
        (mClassName, mInstanceType) = extractClassAndInstanceType constraintType
    in case (mClassName, mInstanceType) of
        (Just className, Just instanceType) ->
            let methodFuncs = map (methodToFunction className instanceType) methods
            in [MetallicInstance className instanceType methodFuncs]
        _ -> []

extractClassAndInstanceType :: Type -> (Maybe String, Maybe Type)
extractClassAndInstanceType (TApp (TConstructor (TypeConstructor classId _)) argTy) =
    (Just (tyUniqueName classId), Just argTy)
extractClassAndInstanceType _ = (Nothing, Nothing)

methodToFunction ::
    String ->
    Type ->
    TypedInstanceMethod ->
    MetallicFunction
methodToFunction _className instanceType (methodName, body, paramTypes, returnType) =
    let mangledName = case methodName of
            NUser baseUnique ->
                -- Create a synthetic name for the instance method
                NSynthetic (SyntheticId baseUnique (SKInstanceMethod instanceType) 0)
            _ ->
                -- Fallback for non-user names (shouldn't happen in practice)
                error $ "methodToFunction: Expected NUser for method name, got: " ++ show methodName
        params = zipWith (\i t -> (NLocal (LocalId LPParam i), t)) [0 :: Int ..] paramTypes
        metadata = MetallicFunctionMetadata [] [] Nothing Nothing defaultFunctionAttributes
    in MetallicFunction mangledName params returnType body metadata
