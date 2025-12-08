{-# LANGUAGE NamedFieldPuns #-}

module Llvm.Gen.Entry (
    compileLlvmModule,
    runLlvmCodeGen,
    runLlvmCodeGenAndTranscribe,
) where

import Alloy.Ir (AlloyConstructor (..), AlloyFunction (..), AlloyModule (AlloyModule, amFunctions, amName, amStructTypes, amTypeDefs), AlloyTypeDef (..))
import qualified Data.Map.Strict as Map
import qualified Data.Set
import Llvm.Gen.Core (IrGen, StructTypeInfo (..), globalDefaultState, irDependencies, irFunctions, namedDefaultEnv, runIrGen)
import Llvm.Gen.Function (compileFunction)
import Llvm.Gen.TypeConversion (convertTypeWithStructs)
import Llvm.Ir (IR (toLlvm))
import Llvm.Modules (LlvmModule (..), LlvmTypeDef (..))
import Project.Name (Name (..))
import qualified Project.Name
import qualified Project.Unique

compileLlvmModule :: AlloyModule -> IrGen ()
compileLlvmModule AlloyModule{amFunctions} = do
    -- Only compile concrete monomorphized functions to LLVM
    let concreteFunctions = filter isConcreteFunction amFunctions
    mapM_ compileFunction concreteFunctions
  where
    isConcreteFunction :: AlloyFunction -> Bool
    isConcreteFunction AlloyFunction{afConstraints = constraints} = null constraints

runLlvmCodeGen :: AlloyModule -> LlvmModule
runLlvmCodeGen alloyModule@AlloyModule{amName = name, amStructTypes = structs, amTypeDefs = typeDefs} =
    let
        structInfoMap = buildStructTypeInfoMap structs typeDefs
        env = namedDefaultEnv name structs structInfoMap

        ((_, _collectedStatements), finalStat) =
            runIrGen env globalDefaultState (compileLlvmModule alloyModule)
        fns = irFunctions finalStat
        deps = irDependencies finalStat
        llvmTypeDefs = concatMap (convertTypeDef structs) typeDefs
    in
        LlvmModule name fns deps [] llvmTypeDefs

buildStructTypeInfoMap :: Data.Set.Set Project.Unique.Unique -> [AlloyTypeDef] -> Map.Map Project.Unique.Unique StructTypeInfo
buildStructTypeInfoMap structs typeDefs =
    Map.fromList
        [ (unique, StructTypeInfo llvmName fieldTypes)
        | AlloyTypeDef{atName, atConstructors, atIsStruct} <- typeDefs
        , atIsStruct
        , [ctor] <- [atConstructors]
        , let llvmName = Project.Name.nameToLLVM atName
              fieldTypes =
                map (convertTypeWithStructs structs) (acCtorFieldTypes ctor)
        , NUser unique <- [atName]
        ]

convertTypeDef :: Data.Set.Set Project.Unique.Unique -> AlloyTypeDef -> [LlvmTypeDef]
convertTypeDef structs AlloyTypeDef{atName, atConstructors, atIsStruct}
    | atIsStruct = case atConstructors of
        [ctor] ->
            let fieldTypes = map (convertTypeWithStructs structs) (acCtorFieldTypes ctor)
                typeName = Project.Name.nameToLLVM atName
            in [LlvmTypeDef typeName fieldTypes]
        _ -> [] -- Structs should have exactly one constructor
    | otherwise = [] -- For now, skip ADTs (they use tag + payload representation)

runLlvmCodeGenAndTranscribe :: AlloyModule -> String
runLlvmCodeGenAndTranscribe alloy =
    let moduleResult = runLlvmCodeGen alloy
        baseIR = toLlvm moduleResult
    in baseIR
