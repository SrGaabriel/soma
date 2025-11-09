module Metal.Gen.Entry where

import Control.Monad.State (gets, modify)
import qualified Data.Map as Map

import Alloy.Naming (makeInstanceMethodName, nameArrayPrefix)
import Inference.Core (TypeMap)
import Metal.Function (MetallicFunction (..))
import Metal.Gen.Binding (metallizeBinding)
import Metal.Gen.Core (
    MetalGen,
    MetalGenState (..),
    addTypeClass,
    defaultMetalState,
    envWithConstructorsFrom,
    metalFunctions,
    metalInstanceMethods,
    metalTypeClasses,
    metalTypes,
    runMetalGen,
 )
import Metal.Gen.DataTypes (compileDataTypeDefsFromRoot)
import Metal.Gen.Extracts (groupInstanceMethods)
import Metal.Metadata (MetallicTypeClassMetadata (..))
import Metal.Module (MetallicModule (..))
import Syntax.Tree (Expr (..), exprChildren)
import Typing.Types (QualifiedType (..), TyConstructor (..), Type (..))

metallizeModule :: String -> Expr -> MetalGen MetallicModule
metallizeModule _ root = do
    compileDataTypeDefsFromRoot root

    let topLevelMembers = exprChildren root

    mapM_ metallizeTypeClass [tc | tc@(ExprTypeClassDef{}) <- topLevelMembers]

    mapM_ metallizeBinding [b | b@(ExprBindingDef{}) <- topLevelMembers]

    mapM_ metallizeInstance [inst | inst@(ExprInstanceDef{}) <- topLevelMembers]

    funcs <- gets metalFunctions
    types <- gets metalTypes
    instances <- gets metalInstanceMethods
    typeClasses <- gets metalTypeClasses

    pure
        MetallicModule
            { mmFunctions = Map.elems funcs
            , mmTypes = Map.elems types
            , mmInstances = groupInstanceMethods instances
            , mmTypeClasses = Map.elems typeClasses
            }

metallizeInstance :: Expr -> MetalGen ()
metallizeInstance (ExprInstanceDef constraintType methods _) =
    case extractInstanceTypeName constraintType of
        Just typeName -> mapM_ (metallizeInstanceMethod typeName) methods
        Nothing -> pure () -- Skip fully polymorphic instances (no type constructor)
  where
    extractInstanceTypeName :: Type -> Maybe String
    extractInstanceTypeName (TApp (TConstructor (TypeConstructor _className _)) argTy) =
        case extractFullTypeName argTy of
            Just argName -> Just argName
            Nothing -> extractPolyTypeName argTy
    extractInstanceTypeName (TConstructor (TypeConstructor name _)) = Just name
    extractInstanceTypeName (TVar _) = Nothing -- Fully polymorphic instance (no type constructor)
    extractInstanceTypeName _ = Nothing

    extractFullTypeName :: Type -> Maybe String
    extractFullTypeName (TApp (TConstructor (TypeConstructor "Array" _)) elemTy) =
        case extractFullTypeName elemTy of
            Just elemName -> Just (nameArrayPrefix ++ elemName)
            Nothing -> Nothing
    extractFullTypeName (TConstructor (TypeConstructor name _)) = Just name
    extractFullTypeName (TVar _) = Nothing
    extractFullTypeName _ = Nothing

    -- Extract polymorphic type constructor name (e.g., "Array" for [a])
    extractPolyTypeName :: Type -> Maybe String
    extractPolyTypeName (TApp (TConstructor (TypeConstructor "Array" _)) (TVar _)) = Just "Array"
    extractPolyTypeName (TConstructor (TypeConstructor name _)) = Just name
    extractPolyTypeName _ = Nothing

    metallizeInstanceMethod :: String -> Expr -> MetalGen ()
    metallizeInstanceMethod typeName bind@(ExprBindingDef name _ _ _ _) = do
        metallizeBinding bind
        let mangledName = makeInstanceMethodName name typeName
        funcs <- gets metalFunctions
        case Map.lookup name funcs of
            Just func -> modify $ \s ->
                s
                    { metalFunctions =
                        Map.insert
                            mangledName
                            (func{mfName = mangledName})
                            (Map.delete name (metalFunctions s))
                    }
            Nothing -> pure ()
    metallizeInstanceMethod _ _ = pure ()
metallizeInstance _ = pure ()

metallizeTypeClass :: Expr -> MetalGen ()
metallizeTypeClass (ExprTypeClassDef className generics methods _) = do
    let methodBindings = [(extractMethodName method, extractMethodType method) | method <- methods]
    let tcMeta =
            MetallicTypeClassMetadata
                { mtcName = className
                , mtcTypeVars = generics
                , mtcMethods = methodBindings
                }
    addTypeClass className tcMeta
  where
    extractMethodName :: Expr -> String
    extractMethodName (ExprTypeClassBinding name _ _ _) = name
    extractMethodName _ = ""

    extractMethodType :: Expr -> QualifiedType
    extractMethodType (ExprTypeClassBinding _ qtype _ _) = qtype
    extractMethodType _ = Forall [] [] (TConstructor (TypeConstructor "Unknown" undefined))
metallizeTypeClass _ = pure ()

compileMetalModule :: String -> Expr -> TypeMap -> MetallicModule
compileMetalModule name root typeMap =
    let env = envWithConstructorsFrom name typeMap root
        (metalModule, _) = runMetalGen env defaultMetalState (metallizeModule name root)
    in metalModule
