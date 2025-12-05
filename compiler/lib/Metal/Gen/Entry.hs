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
import Inference.Core (TypedBinding)
import Metal.Expr (TypedExpr)
import Metal.Function (MetallicFunction (..))
import Metal.Metadata (MetallicConstructorMetadata, MetallicFunctionMetadata (MetallicFunctionMetadata), MetallicTypeClassMetadata, defaultFunctionAttributes)
import Metal.Module (MetallicInstance (..), MetallicModule (..), MetallicTypeDef)
import Metal.Naming (makeInstanceMethodName, nameArrayPrefix)
import Typing.Types (QualifiedType (..), TyConstructor (..), Type (..))

data TypedLowerResult = TypedLowerResult
    { tlrBindings :: [TypedBinding]
    , tlrTypes :: [MetallicTypeDef]
    , tlrInstances :: [(QualifiedType, [(String, TypedExpr, [Type], Type)])]
    , tlrTypeClasses :: [MetallicTypeClassMetadata]
    }
    deriving (Show)

compileMetalModule ::
    String ->
    TypedLowerResult ->
    Map.Map String MetallicConstructorMetadata ->
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
    let params = zipWith (\i t -> ("arg" ++ show i, t)) [0 :: Int ..] paramTypes
        metadata = MetallicFunctionMetadata typeVars constraints Nothing Nothing attrs
    in MetallicFunction name params returnType body metadata

instanceToMetallicInstance ::
    (QualifiedType, [(String, TypedExpr, [Type], Type)]) ->
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
extractClassAndInstanceType (TApp (TConstructor (TypeConstructor className _)) argTy) =
    (Just className, Just argTy)
extractClassAndInstanceType _ = (Nothing, Nothing)

methodToFunction ::
    String ->
    Type ->
    (String, TypedExpr, [Type], Type) ->
    MetallicFunction
methodToFunction _className instanceType (methodName, body, paramTypes, returnType) =
    let typeName = extractTypeName instanceType
        mangledName = makeInstanceMethodName methodName typeName
        params = zipWith (\i t -> ("arg" ++ show i, t)) [0 :: Int ..] paramTypes
        metadata = MetallicFunctionMetadata [] [] Nothing Nothing defaultFunctionAttributes
    in MetallicFunction mangledName params returnType body metadata

extractTypeName :: Type -> String
extractTypeName (TApp (TConstructor (TypeConstructor "Array" _)) elemTy) =
    nameArrayPrefix ++ extractTypeName elemTy
extractTypeName (TApp (TConstructor (TypeConstructor name _)) _) = name
extractTypeName (TConstructor (TypeConstructor name _)) = name
extractTypeName (TVar _) = "Poly"
extractTypeName _ = "Unknown"
