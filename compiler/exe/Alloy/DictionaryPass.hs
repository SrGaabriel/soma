{-# LANGUAGE LambdaCase #-}

module Alloy.DictionaryPass (
    transformModuleWithDictionaries,
) where

import Alloy.DictUtils (
    extractClassName,
    extractInstanceType,
    parseInstanceMethodName,
 )
import Alloy.Ir (
    ABlock (..),
    ACallable (..),
    AInstr (..),
    AOp (..),
    AOperand (..),
    AlloyFunction (..),
    AlloyModule (..),
    DictionaryDef (..),
    Name,
 )
import Alloy.Naming (
    makeDictGlobalName,
    makeDictParamName,
    makeDictStructTypeName,
 )
import Data.List (nub)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, mapMaybe)
import Metal.Metadata (MetallicTypeClassMetadata (..))
import Typing.Types (
    Constraint (..),
    Kind (..),
    TyConstructor (..),
    Type (..),
 )

type TypeEnv = Map Name Type

transformModuleWithDictionaries :: AlloyModule -> AlloyModule
transformModuleWithDictionaries m@AlloyModule{amName = moduleName, amFunctions = funcs, amDictionaries = existingDicts, amTypeClasses = typeClasses} =
    let
        instanceMap = buildInstanceMap funcs typeClasses
        methodToClass = buildMethodToClassMap typeClasses
        classToMethods = buildClassToMethodsMap typeClasses
        funcSigMap = buildFunctionSignatureMap funcs
        newDictionaries = generateDictionaries moduleName typeClasses instanceMap
        (polyFuncs, monoFuncs) = partitionFunctions funcs
        transformedPolyFuncs = map (transformPolyFunction moduleName typeClasses methodToClass classToMethods) polyFuncs
        transformedMonoFuncs = map (transformMonoFunction moduleName typeClasses methodToClass classToMethods instanceMap funcSigMap) monoFuncs
        allFuncs = transformedMonoFuncs ++ transformedPolyFuncs
        allDicts = existingDicts ++ newDictionaries
    in
        m{amFunctions = allFuncs, amDictionaries = allDicts}

buildInstanceMap :: [AlloyFunction] -> [MetallicTypeClassMetadata] -> Map (String, Type, String) Name
buildInstanceMap funcs typeClasses =
    Map.fromList
        [ ((className, instanceType, methodName), afName func)
        | func <- funcs
        , Just (methodName, typeName) <-
            [ parseInstanceMethodName
                (afName func)
            ]
        , let instanceType = parseTypeFromName typeName
        , Just className <- [findClassForMethod methodName typeClasses]
        ]
  where
    findClassForMethod :: String -> [MetallicTypeClassMetadata] -> Maybe String
    findClassForMethod methodName tcs =
        case [mtcName tc | tc <- tcs, (mname, _) <- mtcMethods tc, mname == methodName] of
            (className : _) -> Just className
            [] -> Nothing

    parseTypeFromName :: String -> Type
    parseTypeFromName name =
        case break (== '$') name of
            ("Array", '$' : rest) ->
                TApp (TConstructor (TypeConstructor "Array" KindStar)) (parseTypeFromName rest)
            (base, '$' : rest) ->
                TApp (TConstructor (TypeConstructor base KindStar)) (parseTypeFromName rest)
            (base, "") ->
                TConstructor (TypeConstructor base KindStar)
            _ -> TConstructor (TypeConstructor name KindStar)

buildMethodToClassMap :: [MetallicTypeClassMetadata] -> Map String String
buildMethodToClassMap typeClasses =
    Map.fromList
        [ (methodName, mtcName tc)
        | tc <- typeClasses
        , (methodName, _) <- mtcMethods tc
        ]

buildClassToMethodsMap :: [MetallicTypeClassMetadata] -> Map String [(Int, String)]
buildClassToMethodsMap typeClasses =
    Map.fromList
        [ (mtcName tc, zip [0 ..] [methodName | (methodName, _) <- mtcMethods tc])
        | tc <- typeClasses
        ]

buildFunctionSignatureMap :: [AlloyFunction] -> Map Name ([Type], [Constraint])
buildFunctionSignatureMap funcs =
    Map.fromList
        [ (afName func, (map snd (afParams func), afConstraints func))
        | func <- funcs
        ]

generateDictionaries :: String -> [MetallicTypeClassMetadata] -> Map (String, Type, String) Name -> [DictionaryDef]
generateDictionaries _moduleName typeClasses instanceMap =
    [ DictionaryDef
        { ddClassName = mtcName tc
        , ddForType = instanceType
        , ddMethods =
            [ (methodName, implFunc)
            | (methodName, _) <- mtcMethods tc
            , Just implFunc <- [Map.lookup (mtcName tc, instanceType, methodName) instanceMap]
            ]
        }
    | tc <- typeClasses
    , instanceType <- nub [ty | ((className, ty, _), _) <- Map.toList instanceMap, className == mtcName tc]
    , let hasAllMethods =
            all
                (\(methodName, _) -> Map.member (mtcName tc, instanceType, methodName) instanceMap)
                (mtcMethods tc)
    , hasAllMethods
    ]

partitionFunctions :: [AlloyFunction] -> ([AlloyFunction], [AlloyFunction])
partitionFunctions funcs =
    let polyFuncs = [f | f <- funcs, not (null (afConstraints f))]
        monoFuncs = [f | f <- funcs, null (afConstraints f)]
    in (polyFuncs, monoFuncs)

transformPolyFunction ::
    String ->
    [MetallicTypeClassMetadata] ->
    Map String String ->
    Map String [(Int, String)] ->
    AlloyFunction ->
    AlloyFunction
transformPolyFunction moduleName typeClasses methodToClass classToMethods func@AlloyFunction{afConstraints = constraints, afParams = params, afBlocks = blocks} =
    let
        dictParams = concatMap (constraintToDictParams moduleName) constraints
        dictEnv = buildDictEnv moduleName constraints typeClasses classToMethods dictParams
        initialTypeEnv = Map.fromList (dictParams ++ params)
        newBlocks = map (transformBlock dictEnv methodToClass initialTypeEnv) blocks
    in
        func{afParams = dictParams ++ params, afBlocks = newBlocks}

transformMonoFunction ::
    String ->
    [MetallicTypeClassMetadata] ->
    Map String String ->
    Map String [(Int, String)] ->
    Map (String, Type, String) Name ->
    Map Name ([Type], [Constraint]) ->
    AlloyFunction ->
    AlloyFunction
transformMonoFunction moduleName typeClasses _methodToClass classToMethods instanceMap funcSigMap func@AlloyFunction{afParams = params, afBlocks = blocks} =
    let
        initialTypeEnv = Map.fromList params
        completeTypeEnv = buildCompleteTypeEnv initialTypeEnv blocks
        newBlocks = map (transformBlockForCalls moduleName funcSigMap instanceMap typeClasses classToMethods completeTypeEnv) blocks
    in
        func{afBlocks = newBlocks}

buildCompleteTypeEnv :: TypeEnv -> [ABlock] -> TypeEnv
buildCompleteTypeEnv = foldl addBlockVars
  where
    addBlockVars :: TypeEnv -> ABlock -> TypeEnv
    addBlockVars env ABlock{abParams = blkParams, abInstrs = instrs} =
        let envWithParams = Map.union (Map.fromList blkParams) env
            envWithInstrs = foldl addInstrVars envWithParams instrs
        in envWithInstrs

    addInstrVars :: TypeEnv -> AInstr -> TypeEnv
    addInstrVars env (ILet name ty _) = Map.insert name ty env
    addInstrVars env (IEffect _) = env

constraintToDictParams :: String -> Constraint -> [(Name, Type)]
constraintToDictParams moduleName (Constraint constraintType) =
    case extractClassName constraintType of
        Just className ->
            case extractInstanceType constraintType of
                Just instanceTy ->
                    let paramName = makeDictParamName className instanceTy
                        paramType = TConstructor (TypeConstructor (makeDictStructTypeName moduleName className) KindStar)
                    in [(paramName, paramType)]
                Nothing -> []
        Nothing -> []

buildDictEnv ::
    String ->
    [Constraint] ->
    [MetallicTypeClassMetadata] ->
    Map String [(Int, String)] ->
    [(Name, Type)] ->
    Map String (Name, Int)
buildDictEnv moduleName constraints _typeClasses classToMethods dictParams =
    Map.fromList
        [ (methodName, (dictParamName, methodIdx))
        | Constraint cty <- constraints
        , Just className <- [extractClassName cty]
        , Just instanceTy <- [extractInstanceType cty]
        , let dictParamName = makeDictParamName className instanceTy
        , let dictParamType = TConstructor (TypeConstructor (makeDictStructTypeName moduleName className) KindStar)
        , (dictParamName, dictParamType) `elem` dictParams
        , (methodIdx, methodName) <- fromMaybe [] (Map.lookup className classToMethods)
        ]

transformBlock :: Map String (Name, Int) -> Map String String -> TypeEnv -> ABlock -> ABlock
transformBlock dictEnv methodToClass typeEnv block@ABlock{abInstrs = instrs, abParams = blockParams} =
    let
        extendedTypeEnv = Map.union (Map.fromList blockParams) typeEnv
        (newInstrs, _finalTypeEnv) = transformInstrs dictEnv methodToClass extendedTypeEnv instrs
    in
        block{abInstrs = newInstrs}

transformInstrs :: Map String (Name, Int) -> Map String String -> TypeEnv -> [AInstr] -> ([AInstr], TypeEnv)
transformInstrs dictEnv methodToClass typeEnv =
    foldl
        ( \(accInstrs, accEnv) instr ->
            let (newInstr, newEnv) = transformInstr dictEnv methodToClass accEnv instr
            in (accInstrs ++ [newInstr], newEnv)
        )
        ([], typeEnv)

transformInstr :: Map String (Name, Int) -> Map String String -> TypeEnv -> AInstr -> (AInstr, TypeEnv)
transformInstr dictEnv methodToClass typeEnv instr =
    case instr of
        ILet name ty op ->
            let newOp = transformOp dictEnv methodToClass op
                newTypeEnv = Map.insert name ty typeEnv
            in (ILet name ty newOp, newTypeEnv)
        _ -> (instr, typeEnv)

transformOp :: Map String (Name, Int) -> Map String String -> AOp -> AOp
transformOp dictEnv _methodToClass op =
    case op of
        OpCall (Direct callee) args ->
            case Map.lookup callee dictEnv of
                Just (dictParamName, methodIdx) ->
                    OpDictCall (OpVar dictParamName) methodIdx callee args
                Nothing ->
                    op
        _ -> op

transformBlockForCalls ::
    String ->
    Map Name ([Type], [Constraint]) ->
    Map (String, Type, String) Name ->
    [MetallicTypeClassMetadata] ->
    Map String [(Int, String)] ->
    TypeEnv ->
    ABlock ->
    ABlock
transformBlockForCalls moduleName funcSigMap instanceMap typeClasses classToMethods typeEnv blk@ABlock{abParams = blkParams, abInstrs = instrs} =
    let extendedTypeEnv = Map.union (Map.fromList blkParams) typeEnv
        (newInstrs, _) = transformInstrsForCalls moduleName funcSigMap instanceMap typeClasses classToMethods extendedTypeEnv instrs
    in blk{abInstrs = newInstrs}

transformInstrsForCalls ::
    String ->
    Map Name ([Type], [Constraint]) ->
    Map (String, Type, String) Name ->
    [MetallicTypeClassMetadata] ->
    Map String [(Int, String)] ->
    TypeEnv ->
    [AInstr] ->
    ([AInstr], TypeEnv)
transformInstrsForCalls moduleName funcSigMap instanceMap typeClasses classToMethods typeEnv =
    foldl
        ( \(accInstrs, accEnv) instr ->
            let (newInstr, newEnv) = transformInstrForCalls moduleName funcSigMap instanceMap typeClasses classToMethods accEnv instr
            in (accInstrs ++ [newInstr], newEnv)
        )
        ([], typeEnv)

transformInstrForCalls ::
    String ->
    Map Name ([Type], [Constraint]) ->
    Map (String, Type, String) Name ->
    [MetallicTypeClassMetadata] ->
    Map String [(Int, String)] ->
    TypeEnv ->
    AInstr ->
    (AInstr, TypeEnv)
transformInstrForCalls moduleName funcSigMap instanceMap typeClasses classToMethods typeEnv instr =
    case instr of
        ILet name ty op ->
            let newOp = transformOpForCalls moduleName funcSigMap instanceMap typeClasses classToMethods typeEnv op
                newTypeEnv = Map.insert name ty typeEnv
            in (ILet name ty newOp, newTypeEnv)
        _ -> (instr, typeEnv)

transformOpForCalls ::
    String ->
    Map Name ([Type], [Constraint]) ->
    Map (String, Type, String) Name ->
    [MetallicTypeClassMetadata] ->
    Map String [(Int, String)] ->
    TypeEnv ->
    AOp ->
    AOp
transformOpForCalls moduleName funcSigMap instanceMap typeClasses _classToMethods typeEnv op =
    case op of
        OpCall (Direct callee) args ->
            case findMethodClass callee typeClasses of
                Just className ->
                    case args of
                        (firstArg : _) ->
                            case inferOperandType typeEnv firstArg of
                                Just argType ->
                                    case findInstanceForType className callee argType of
                                        Just instanceFunc ->
                                            OpCall (Direct instanceFunc) args
                                        Nothing ->
                                            op
                                Nothing -> op
                        [] -> op
                Nothing ->
                    case Map.lookup callee funcSigMap of
                        Just (paramTypes, constraints)
                            | not (null constraints) ->
                                let argTypes = map (inferOperandType typeEnv) args
                                    dictArgs = buildDictArgsForCall moduleName constraints paramTypes argTypes instanceMap typeClasses
                                in OpCall (Direct callee) (dictArgs ++ args)
                        _ -> op
        _ -> op
  where
    findMethodClass :: String -> [MetallicTypeClassMetadata] -> Maybe String
    findMethodClass methodName tcs =
        case [mtcName tc | tc <- tcs, (mname, _) <- mtcMethods tc, mname == methodName] of
            (className : _) -> Just className
            [] -> Nothing

    findInstanceForType :: String -> String -> Type -> Maybe Name
    findInstanceForType className methodName actualType =
        case Map.lookup (className, actualType, methodName) instanceMap of
            Just func -> Just func
            Nothing ->
                let typeConstructor = extractTypeConstructor actualType
                    matches = [(func, instType) | ((cn, instType, mn), func) <- Map.toList instanceMap, cn == className, mn == methodName]
                    validMatches = [(func, instType) | (func, instType) <- matches, typeConstructorsMatch typeConstructor (extractTypeConstructor instType)]
                in case validMatches of
                    ((func, _) : _) -> Just func
                    [] -> Nothing

    extractTypeConstructor :: Type -> Type
    extractTypeConstructor (TApp tycon _) = tycon
    extractTypeConstructor ty = ty

    typeConstructorsMatch :: Type -> Type -> Bool
    typeConstructorsMatch (TConstructor tc1) (TConstructor tc2) = tcName tc1 == tcName tc2
    typeConstructorsMatch _ _ = False

inferOperandType :: TypeEnv -> AOperand -> Maybe Type
inferOperandType typeEnv = \case
    OpVar name -> Map.lookup name typeEnv
    OpConst _ -> Nothing

buildDictArgsForCall ::
    String ->
    [Constraint] ->
    [Type] ->
    [Maybe Type] ->
    Map (String, Type, String) Name ->
    [MetallicTypeClassMetadata] ->
    [AOperand]
buildDictArgsForCall moduleName constraints paramTypes argTypes _instanceMap _typeClasses =
    mapMaybe buildDictArg constraints
  where
    buildDictArg :: Constraint -> Maybe AOperand
    buildDictArg (Constraint constraintType) = do
        className <- extractClassName constraintType
        constraintInstanceType <- extractInstanceType constraintType
        concreteType <- resolveConstraintType constraintInstanceType paramTypes argTypes
        let dictGlobalName = makeDictGlobalName moduleName className concreteType
        return $ OpVar dictGlobalName

    resolveConstraintType :: Type -> [Type] -> [Maybe Type] -> Maybe Type
    resolveConstraintType constraintTy paramTys argTys =
        case constraintTy of
            -- if it's a type variable, find which parameter it corresponds to and get actual type
            TVar tv ->
                let matches = findMatchingArgType (TVar tv) paramTys argTys
                in case matches of
                    (actualType : _) -> Just actualType
                    [] -> Nothing
            -- if it's already concrete use it directly
            TConstructor _ -> Just constraintTy
            TApp _ _ -> Just constraintTy
            _ -> Nothing

    findMatchingArgType :: Type -> [Type] -> [Maybe Type] -> [Type]
    findMatchingArgType targetVar paramTys argTys =
        [ actualType
        | (paramType, Just actualType) <- zip paramTys argTys
        , typesMatch targetVar paramType
        ]
