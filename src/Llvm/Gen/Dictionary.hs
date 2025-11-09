module Llvm.Gen.Dictionary (
    compileDictionaries,
    getDictionaryGlobalName,
) where

import Alloy.Ir (AlloyFunction (..), DictionaryDef (..), Name)
import Data.List (intercalate, nub)
import qualified Data.Map.Strict as Map
import Llvm.Gen.TypeConversion (convertType)
import Llvm.Ir (IR (toLlvm))
import Llvm.Modules (LlvmGlobal (..))
import Llvm.Types (LlvmType (..))
import qualified Llvm.Types as LT
import Typing.Types (SkolemVar (SkolemVar, skId), TyConstructor (TypeConstructor, tcName), TyVar (TypeVar, tvId), Type (..))

compileDictionaries ::
    [DictionaryDef] ->
    [AlloyFunction] ->
    ([String], [LlvmGlobal], Map.Map (String, Type) String)
compileDictionaries dicts allFunctions =
    let
        typeClassStructDecls = generateTypeClassStructDeclarations dicts allFunctions
        (dictGlobals, dictMapEntries) = unzip [generateDictionaryGlobal dict allFunctions | dict <- dicts]
        dictLookupMap = Map.fromList dictMapEntries
    in
        (typeClassStructDecls, dictGlobals, dictLookupMap)

generateTypeClassStructDeclarations :: [DictionaryDef] -> [AlloyFunction] -> [String]
generateTypeClassStructDeclarations dicts allFunctions =
    let
        uniqueClasses = nub [ddClassName dict | dict <- dicts]
        classToDict = Map.fromList [(ddClassName dict, dict) | dict <- dicts]
    in
        [generateTypeClassStructDecl className (classToDict Map.! className) allFunctions | className <- uniqueClasses]

generateTypeClassStructDecl :: String -> DictionaryDef -> [AlloyFunction] -> String
generateTypeClassStructDecl className dict allFunctions =
    let
        structName = className ++ "$Dict"
        methods = ddMethods dict
        fieldTypes = [getFunctionPointerType methodImpl allFunctions | (_methodName, methodImpl) <- methods]
        fieldsStr = intercalate ", " (map toLlvm fieldTypes)
    in
        "%" ++ structName ++ " = type { " ++ fieldsStr ++ " }"

getFunctionPointerType :: Name -> [AlloyFunction] -> LlvmType
getFunctionPointerType fnName allFunctions =
    case [f | f <- allFunctions, afName f == fnName] of
        (AlloyFunction{afParams = params, afReturnType = retType} : _) ->
            let paramTypes = map (convertType . snd) params
                llvmRetType = convertType retType
            in LT.LlvmFunctionPtr llvmRetType paramTypes
        [] ->
            -- fallback: generic function pointer (i8*)
            LT.LlvmPtr LlvmI8

generateDictionaryGlobal :: DictionaryDef -> [AlloyFunction] -> (LlvmGlobal, ((String, Type), String))
generateDictionaryGlobal DictionaryDef{ddClassName = className, ddForType = forType, ddMethods = methods} allFunctions =
    let
        dictName = "dict$" ++ className ++ "$" ++ sanitizeType forType
        structTypeName = className ++ "$Dict"
        structType = LT.LlvmNamed structTypeName

        methodInitializers =
            [ getFunctionPointerInitializer methodImpl allFunctions
            | (_methodName, methodImpl) <- methods
            ]

        initializer =
            if null methodInitializers
                then "zeroinitializer"
                else "{ " ++ intercalate ", " methodInitializers ++ " }"

        globalDef =
            LlvmGlobal
                { globalName = dictName
                , globalType = structType
                , globalConstant = True
                , globalInitializer = initializer
                , globalLinkage = "internal"
                }

        lookupKey = ((className, forType), dictName)
    in
        (globalDef, lookupKey)

getFunctionPointerInitializer :: Name -> [AlloyFunction] -> String
getFunctionPointerInitializer fnName allFunctions =
    case [f | f <- allFunctions, afName f == fnName] of
        (AlloyFunction{afParams = params, afReturnType = retType} : _) ->
            let paramTypes = map (convertType . snd) params
                llvmRetType = convertType retType
                paramTypesStr = intercalate ", " (map toLlvm paramTypes)
                signature = toLlvm llvmRetType ++ " (" ++ paramTypesStr ++ ")"
            in signature ++ "* @" ++ fnName
        [] ->
            "i8* null"

sanitizeType :: Type -> String
sanitizeType (TConstructor (TypeConstructor{tcName = name})) = name
sanitizeType (TApp (TConstructor (TypeConstructor{tcName = "Array"})) elemTy) =
    "Array$" ++ sanitizeType elemTy
sanitizeType (TApp f arg) = sanitizeType f ++ "$" ++ sanitizeType arg
sanitizeType (TVar (TypeVar{tvId = name})) = "T" ++ name
sanitizeType (TSkolem (SkolemVar{skId = name})) = "S" ++ name
sanitizeType _ = "Unknown"

getDictionaryGlobalName :: String -> Type -> Map.Map (String, Type) String -> Maybe String
getDictionaryGlobalName className instanceType = Map.lookup (className, instanceType)
