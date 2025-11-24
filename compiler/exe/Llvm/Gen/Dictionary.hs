module Llvm.Gen.Dictionary (
    compileDictionaries,
    getDictionaryGlobalName,
) where

import Alloy.Ir (AlloyFunction (..), DictionaryDef (..), Name)
import Alloy.Naming (
    makeDictGlobalName,
    makeDictStructTypeName,
    qualifyWithModule,
 )
import Data.List (intercalate, nub)
import qualified Data.Map.Strict as Map
import Llvm.Ir (IR (toLlvm))
import Llvm.Modules (LlvmGlobal (..))
import Llvm.Types (LlvmType (..))
import qualified Llvm.Types as LT
import Typing.Types (Type)

compileDictionaries ::
    String ->
    [DictionaryDef] ->
    [AlloyFunction] ->
    ([String], [LlvmGlobal], Map.Map (String, Type) String)
compileDictionaries moduleName dicts allFunctions =
    let
        typeClassStructDecls = generateTypeClassStructDeclarations moduleName dicts allFunctions
        (dictGlobals, dictMapEntries) = unzip [generateDictionaryGlobal moduleName dict | dict <- dicts]
        dictLookupMap = Map.fromList dictMapEntries
    in
        (typeClassStructDecls, dictGlobals, dictLookupMap)

generateTypeClassStructDeclarations :: String -> [DictionaryDef] -> [AlloyFunction] -> [String]
generateTypeClassStructDeclarations moduleName dicts _allFunctions =
    let
        uniqueClasses = nub [ddClassName dict | dict <- dicts]
        classToDict = Map.fromList [(ddClassName dict, dict) | dict <- dicts]
    in
        [generateTypeClassStructDecl moduleName className (classToDict Map.! className) | className <- uniqueClasses]

generateTypeClassStructDecl :: String -> String -> DictionaryDef -> String
generateTypeClassStructDecl moduleName className dict =
    let
        structName = makeDictStructTypeName moduleName className
        methods = ddMethods dict
        fieldTypes = [getFunctionPointerType methodImpl | (_methodName, methodImpl) <- methods]
        fieldsStr = intercalate ", " (map toLlvm fieldTypes)
    in
        "%" ++ structName ++ " = type { " ++ fieldsStr ++ " }"

getFunctionPointerType :: Name -> LlvmType
getFunctionPointerType _fnName =
    LT.LlvmPtr LlvmI8

generateDictionaryGlobal :: String -> DictionaryDef -> (LlvmGlobal, ((String, Type), String))
generateDictionaryGlobal moduleName DictionaryDef{ddClassName = className, ddForType = forType, ddMethods = methods} =
    let
        dictName = makeDictGlobalName moduleName className forType
        structTypeName = makeDictStructTypeName moduleName className
        structType = LT.LlvmNamed structTypeName

        methodInitializers =
            [ getFunctionPointerInitializer moduleName methodImpl
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

getFunctionPointerInitializer :: String -> Name -> String
getFunctionPointerInitializer moduleName fnName =
    let qualifiedName = qualifyWithModule moduleName fnName
    in "i8* @" ++ qualifiedName

getDictionaryGlobalName :: String -> Type -> Map.Map (String, Type) String -> Maybe String
getDictionaryGlobalName className instanceType = Map.lookup (className, instanceType)
