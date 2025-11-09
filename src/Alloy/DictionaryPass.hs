{-# LANGUAGE LambdaCase #-}

module Alloy.DictionaryPass (
    transformModuleWithDictionaries,
) where

import Alloy.DictUtils (
    extractClassName,
    extractInstanceType,
    makeDictGlobalName,
    makeDictParamName,
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
transformModuleWithDictionaries m@AlloyModule{amFunctions = funcs, amDictionaries = existingDicts, amTypeClasses = typeClasses} =
    let
        instanceMap = buildInstanceMap funcs typeClasses
        methodToClass = buildMethodToClassMap typeClasses
        classToMethods = buildClassToMethodsMap typeClasses
        funcSigMap = buildFunctionSignatureMap funcs
        newDictionaries = generateDictionaries typeClasses instanceMap
        (polyFuncs, monoFuncs) = partitionFunctions funcs
        transformedPolyFuncs = map (transformPolyFunction typeClasses methodToClass classToMethods) polyFuncs
        transformedMonoFuncs = map (transformMonoFunction typeClasses methodToClass classToMethods instanceMap funcSigMap) monoFuncs
        allFuncs = transformedMonoFuncs ++ transformedPolyFuncs
        allDicts = existingDicts ++ newDictionaries
    in
        m{amFunctions = allFuncs, amDictionaries = allDicts}

buildInstanceMap :: [AlloyFunction] -> [MetallicTypeClassMetadata] -> Map (String, Type, String) Name
buildInstanceMap funcs typeClasses =
    Map.fromList
        [((className, instanceType, methodName), afName func) |
           func <- funcs,
           Just (methodName, typeName) <- [parseInstanceMethodName
                                             (afName func)],
           let instanceType = parseTypeFromName typeName,
           Just className <- [findClassForMethod methodName typeClasses]]
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

generateDictionaries :: [MetallicTypeClassMetadata] -> Map (String, Type, String) Name -> [DictionaryDef]
generateDictionaries typeClasses instanceMap =
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
    [MetallicTypeClassMetadata] ->
    Map String String ->
    Map String [(Int, String)] ->
    AlloyFunction ->
    AlloyFunction
transformPolyFunction typeClasses methodToClass classToMethods func@AlloyFunction{afConstraints = constraints, afParams = params, afBlocks = blocks} =
    let
        dictParams = concatMap constraintToDictParams constraints
        dictEnv = buildDictEnv constraints typeClasses classToMethods dictParams
        initialTypeEnv = Map.fromList (dictParams ++ params)
        newBlocks = map (transformBlock dictEnv methodToClass initialTypeEnv) blocks
    in
        func{afParams = dictParams ++ params, afBlocks = newBlocks}

transformMonoFunction ::
    [MetallicTypeClassMetadata] ->
    Map String String ->
    Map String [(Int, String)] ->
    Map (String, Type, String) Name ->
    Map Name ([Type], [Constraint]) ->
    AlloyFunction ->
    AlloyFunction
transformMonoFunction typeClasses _methodToClass classToMethods instanceMap funcSigMap func@AlloyFunction{afParams = params, afBlocks = blocks} =
    let
        initialTypeEnv = Map.fromList params
        newBlocks = map (transformBlockForCalls funcSigMap instanceMap typeClasses classToMethods initialTypeEnv) blocks
    in
        func{afBlocks = newBlocks}

constraintToDictParams :: Constraint -> [(Name, Type)]
constraintToDictParams (Constraint constraintType) =
    case extractClassName constraintType of
        Just className ->
            case extractInstanceType constraintType of
                Just instanceTy ->
                    let paramName = makeDictParamName className instanceTy
                        paramType = TConstructor (TypeConstructor (className ++ "$Dict") KindStar)
                    in [(paramName, paramType)]
                Nothing -> []
        Nothing -> []

buildDictEnv ::
    [Constraint] ->
    [MetallicTypeClassMetadata] ->
    Map String [(Int, String)] ->
    [(Name, Type)] ->
    Map String (Name, Int)
buildDictEnv constraints _typeClasses classToMethods dictParams =
    Map.fromList
        [ (methodName, (dictParamName, methodIdx))
        | Constraint cty <- constraints
        , Just className <- [extractClassName cty]
        , Just instanceTy <- [extractInstanceType cty]
        , let dictParamName = makeDictParamName className instanceTy
        , let dictParamType = TConstructor (TypeConstructor (className ++ "$Dict") KindStar)
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
    Map Name ([Type], [Constraint]) ->
    Map (String, Type, String) Name ->
    [MetallicTypeClassMetadata] ->
    Map String [(Int, String)] ->
    TypeEnv ->
    ABlock ->
    ABlock
transformBlockForCalls funcSigMap instanceMap typeClasses classToMethods typeEnv block@ABlock{abInstrs = instrs, abParams = blockParams} =
    let
        extendedTypeEnv = Map.union (Map.fromList blockParams) typeEnv
        (newInstrs, _finalTypeEnv) = transformInstrsForCalls funcSigMap instanceMap typeClasses classToMethods extendedTypeEnv instrs
    in
        block{abInstrs = newInstrs}

transformInstrsForCalls ::
    Map Name ([Type], [Constraint]) ->
    Map (String, Type, String) Name ->
    [MetallicTypeClassMetadata] ->
    Map String [(Int, String)] ->
    TypeEnv ->
    [AInstr] ->
    ([AInstr], TypeEnv)
transformInstrsForCalls funcSigMap instanceMap typeClasses classToMethods typeEnv = foldl
        ( \(accInstrs, accEnv) instr ->
            let (newInstr, newEnv) = transformInstrForCalls funcSigMap instanceMap typeClasses classToMethods accEnv instr
            in (accInstrs ++ [newInstr], newEnv)
        )
        ([], typeEnv)

transformInstrForCalls ::
    Map Name ([Type], [Constraint]) ->
    Map (String, Type, String) Name ->
    [MetallicTypeClassMetadata] ->
    Map String [(Int, String)] ->
    TypeEnv ->
    AInstr ->
    (AInstr, TypeEnv)
transformInstrForCalls funcSigMap instanceMap typeClasses classToMethods typeEnv instr =
    case instr of
        ILet name ty op ->
            let newOp = transformOpForCalls funcSigMap instanceMap typeClasses classToMethods typeEnv op
                newTypeEnv = Map.insert name ty typeEnv
            in (ILet name ty newOp, newTypeEnv)
        _ -> (instr, typeEnv)

transformOpForCalls ::
    Map Name ([Type], [Constraint]) ->
    Map (String, Type, String) Name ->
    [MetallicTypeClassMetadata] ->
    Map String [(Int, String)] ->
    TypeEnv ->
    AOp ->
    AOp
transformOpForCalls funcSigMap instanceMap typeClasses _classToMethods typeEnv op =
    case op of
        OpCall (Direct callee) args ->
            case Map.lookup callee funcSigMap of
                Just (paramTypes, constraints)
                    | not (null constraints) ->
                        -- This is a call to a polymorphic function
                        -- Infer actual types from arguments and pass dictionaries
                        let argTypes = map (inferOperandType typeEnv) args
                            dictArgs = buildDictArgsForCall constraints paramTypes argTypes instanceMap typeClasses
                        in OpCall (Direct callee) (dictArgs ++ args)
                _ -> op
        _ -> op

inferOperandType :: TypeEnv -> AOperand -> Maybe Type
inferOperandType typeEnv = \case
    OpVar name -> Map.lookup name typeEnv
    OpConst _ -> Nothing -- Could extract from const but not needed for dict inference

buildDictArgsForCall ::
    [Constraint] ->
    [Type] ->
    [Maybe Type] ->
    Map (String, Type, String) Name ->
    [MetallicTypeClassMetadata] ->
    [AOperand]
buildDictArgsForCall constraints paramTypes argTypes _instanceMap _typeClasses =
    mapMaybe buildDictArg constraints
  where
    buildDictArg :: Constraint -> Maybe AOperand
    buildDictArg (Constraint constraintType) = do
        className <- extractClassName constraintType
        constraintInstanceType <- extractInstanceType constraintType
        concreteType <- resolveConstraintType constraintInstanceType paramTypes argTypes
        let dictGlobalName = makeDictGlobalName className concreteType
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

    typesMatch :: Type -> Type -> Bool
    typesMatch (TVar tv1) (TVar tv2) = tv1 == tv2
    typesMatch (TConstructor tc1) (TConstructor tc2) = tc1 == tc2
    typesMatch (TApp f1 a1) (TApp f2 a2) = typesMatch f1 f2 && typesMatch a1 a2
    typesMatch _ _ = False
