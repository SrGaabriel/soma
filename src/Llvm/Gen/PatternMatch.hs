{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Llvm.Gen.PatternMatch where

import Control.Monad.Reader (asks)
import Control.Monad.State (gets, modify)
import Control.Monad.Writer (tell)
import qualified Data.Map as Map

import Data.Maybe (fromMaybe, mapMaybe)

import Alloy.Decisions

import Llvm.Gen.Context
import Llvm.Gen.Core
import Llvm.Gen.Metadata (ConstructorMetadata (..))
import Llvm.Gen.Panic (panic)
import Llvm.Gen.Templates (newStrTemplate)
import Llvm.Gen.Types (toAllocationLlvmType)
import Llvm.Instructions (LlvmInstruction (..), LlvmStatement (..))

import Llvm.Types (LlvmType (..))
import Llvm.Values (LlvmValue (..), byteLiteral, intLiteral)
import Syntax.Patterns (Literal (..), Pattern (..))
import Syntax.Tree (Expr (..))
import Typing.Types (QualifiedType (Forall), Type)

compileDerivedPatternMatch :: IrGenEnv -> (Expr -> IrGen GenValue) -> Expr -> [GenValue] -> (IrGenEnv, IrGen GenValue)
compileDerivedPatternMatch env compileValueFunc expr fnArgRegs =
    let (dag, indexedBodies) = compileExprDerivedPatternMatchToDAG expr
        patterns = extractPatternsFromExpr expr
        action = do
            compileDAG compileValueFunc dag indexedBodies patterns fnArgRegs
    in (env, action)

extractPatternsFromExpr :: Expr -> [[Pattern]]
extractPatternsFromExpr (ExprDerivedPatternMatch arms) =
    map (\(ExprPatternMatchArm pats _ _) -> pats) arms
extractPatternsFromExpr _ = []

compileDAG :: (Expr -> IrGen GenValue) -> DAG -> [Expr] -> [[Pattern]] -> [GenValue] -> IrGen GenValue
compileDAG compileValueFunc dag bodies patterns args = do
    let rootNodeId = dagRoot dag

    compileDAGNode compileValueFunc dag bodies patterns args rootNodeId

compileDAGNode :: (Expr -> IrGen GenValue) -> DAG -> [Expr] -> [[Pattern]] -> [GenValue] -> NodeId -> IrGen GenValue
compileDAGNode compileValueFunc dag bodies patterns args nodeId = do
    let Just node = Map.lookup nodeId (dagNodes dag)

    case node of
        DAGLeaf action -> do
            scope <- asks currentScope
            newScope <- bindPatternVariablesForAction patterns action args scope
            withScope newScope $ do
                let bodyExpr = bodies !! action
                compileValueFunc bodyExpr
        DAGFail -> error "Pattern match failure at runtime"
        DAGSwitch accessor branches defaultCase -> do
            accessorValue <- compileAccessor accessor args

            case branches of
                [] -> case defaultCase of
                    Just defNodeId -> compileDAGNode compileValueFunc dag bodies patterns args defNodeId
                    Nothing -> do
                        currentFn <- asks currentFunction
                        let fnPrefix = fromMaybe "match" currentFn
                        blockNum <- gets nextBlock
                        let defaultLabel = fnPrefix ++ ".default." ++ show blockNum
                        let mergeLabel = fnPrefix ++ ".merge." ++ show (blockNum + 1)
                        modify $ \s -> s{nextBlock = blockNum + 2}
                        tyMap <- gets typeMap
                        let exprType = case bodies of
                                (body : _) -> case Map.lookup body tyMap of
                                    Just (Forall _ _ ty) -> ty
                                    Nothing -> error "Body expression not in type map"
                                [] -> error "No bodies in pattern match"
                        let llvmRetType = toAllocationLlvmType exprType
                        resultPtr <- alloca llvmRetType
                        _ <- enterNewBlock defaultLabel $ do
                            panic "Non-exhaustive pattern match (no default case)"
                            tell [LlvmUnreachable]
                            return ()
                        _ <- setNewBlock mergeLabel
                        loadedResult <- saveInstruction (LlvmLoad resultPtr) llvmRetType
                        return $ mkVariableLoad (mkStackStructAlloc llvmRetType resultPtr) Nothing loadedResult
                _ -> do
                    let branchCount = length branches
                    currentFn <- asks currentFunction
                    let fnPrefix = fromMaybe "match" currentFn

                    blockNum <- gets nextBlock
                    let branchLabels =
                            [ (ctor, fnPrefix ++ ".case." ++ show (blockNum + i), targetNodeId)
                            | (i, (ctor, targetNodeId)) <- zip [0 ..] branches
                            ]
                    let defaultLabel = fnPrefix ++ ".default." ++ show (blockNum + branchCount)
                    let mergeLabel = fnPrefix ++ ".merge." ++ show (blockNum + branchCount + 1)

                    modify $ \s -> s{nextBlock = blockNum + branchCount + 2}

                    tyMap <- gets typeMap
                    let exprType = case bodies of
                            (body : _) -> case Map.lookup body tyMap of
                                Just (Forall _ _ ty) -> ty
                                Nothing -> error "Body expression not in type map"
                            [] -> error "No bodies in pattern match"
                    let llvmRetType = toAllocationLlvmType exprType
                    resultPtr <- alloca llvmRetType

                    case branches of
                        ((DataCtor _ _, _) : _) -> do
                            tag <- extractADTTag accessorValue
                            compileSwitchBranches tag branchLabels defaultLabel
                        ((LitCtor _, _) : _) -> do
                            compileLiteralSwitchBranches accessorValue branchLabels defaultLabel
                        _ -> error "Unsupported constructor type in switch"

                    sequence_
                        [ enterNewBlock label $ do
                            case Map.lookup targetNodeId (dagNodes dag) of
                                Just DAGFail -> do
                                    panic "Pattern match failure at runtime"
                                    tell [LlvmUnreachable]
                                    return ()
                                _ -> do
                                    result <- compileDAGNode compileValueFunc dag bodies patterns args targetNodeId
                                    tell [LlvmStore llvmRetType (gvw result) resultPtr]
                                    tell [LlvmBr mergeLabel]
                                    return ()
                        | (_ctor, label, targetNodeId) <- branchLabels
                        ]

                    case defaultCase of
                        Just defNodeId -> do
                            case Map.lookup defNodeId (dagNodes dag) of
                                Just DAGFail -> do
                                    _ <- enterNewBlock defaultLabel $ do
                                        panic "Pattern match failure at runtime"
                                        tell [LlvmUnreachable]
                                        return ()
                                    return ()
                                _ -> do
                                    _ <- enterNewBlock defaultLabel $ do
                                        result <- compileDAGNode compileValueFunc dag bodies patterns args defNodeId
                                        tell [LlvmStore llvmRetType (gvw result) resultPtr]
                                        tell [LlvmBr mergeLabel]
                                        return result
                                    return ()
                        Nothing -> do
                            _ <- enterNewBlock defaultLabel $ do
                                panic "Non-exhaustive pattern match (no default case)"
                                tell [LlvmUnreachable]
                                return ()
                            return ()

                    _ <- setNewBlock mergeLabel
                    loadedResult <- saveInstruction (LlvmLoad resultPtr) llvmRetType
                    return $ mkVariableLoad (mkStackStructAlloc llvmRetType resultPtr) Nothing loadedResult

compileAccessor :: Accessor -> [GenValue] -> IrGen GenValue
compileAccessor (Root n) args = do
    if n < length args
        then return $ args !! n
        else error $ "Accessor Root " ++ show n ++ " out of bounds"
compileAccessor (Field base fieldIdx) args = do
    baseValue <- compileAccessor base args
    let baseType = getGenValueType baseValue

    basePtr <- case baseType of
        LlvmNamedType _ -> do
            stackPtr <- alloca baseType
            tell [LlvmStore baseType (gvw baseValue) stackPtr]
            return stackPtr
        LlvmPointer _ -> return (gvw baseValue)
        _ -> return (gvw baseValue)

    let structType = case baseType of
            LlvmNamedType name -> LlvmNamedType name
            LlvmPointer t -> t
            t -> t

    tagVal <- extractADTTag baseValue
    typeName <- case structType of
        LlvmNamedType n -> return n
        _ -> error "Field accessor expects a named ADT type"

    consMap <- gets constructorMap
    let allCons = Map.elems consMap
        sameTypeCons =
            [ md
            | md <- allCons
            , constructorMetadataTypeName md == typeName
            ]

    let collectInfo md =
            if fieldIdx < length (constructorMetadataFieldLlvmTypes md)
                then
                    Just
                        ( constructorMetadataTag md
                        , constructorMetadataFieldLlvmTypes md !! fieldIdx
                        , constructorMetadataFieldOffsets md !! fieldIdx
                        )
                else Nothing
        fieldInfos = mapMaybe collectInfo sameTypeCons

    case fieldInfos of
        [] -> error $ "No constructor metadata available for accessor into type " ++ typeName
        ((_, fieldTy0, _) : rest) -> do
            let allSameTy = all (\(_, ty, _) -> ty == fieldTy0) rest
            if not allSameTy
                then error $ "Mismatched field types across constructors for field index " ++ show fieldIdx ++ " in type " ++ typeName
                else do
                    resultPtr <- alloca fieldTy0

                    currentFn <- asks currentFunction
                    blkNum <- gets nextBlock
                    let fnPrefix = fromMaybe "match" currentFn
                        mkCaseLabel i = fnPrefix ++ ".fld.case." ++ show (blkNum + i)
                        defLabel = fnPrefix ++ ".fld.default." ++ show (blkNum + length fieldInfos)
                        mergeLabel = fnPrefix ++ ".fld.merge." ++ show (blkNum + length fieldInfos + 1)

                    modify $ \s -> s{nextBlock = blkNum + length fieldInfos + 2}

                    let cases = [(byteLiteral tag, mkCaseLabel i) | (i, (tag, _, _)) <- zip [0 ..] fieldInfos]
                    tell [LlvmSwitch (gvw tagVal) defLabel cases]

                    arrayPtr <-
                        saveInstruction
                            (LlvmGetElementPtr structType basePtr [intLiteral 0, intLiteral 1] False)
                            (LlvmPointer LlvmI8)

                    sequence_
                        [ enterNewBlock (mkCaseLabel i) $ do
                            offPtr <-
                                saveInstruction
                                    (LlvmGetElementPtr LlvmI8 arrayPtr [intLiteral off] False)
                                    (LlvmPointer LlvmI8)
                            typedPtr <-
                                saveInstruction
                                    (LlvmBitcast offPtr (LlvmPointer fieldTy0))
                                    (LlvmPointer fieldTy0)
                            loaded <- saveInstruction (LlvmLoad typedPtr) fieldTy0
                            tell [LlvmStore fieldTy0 loaded resultPtr]
                            tell [LlvmBr mergeLabel]
                        | (i, (_tagV, _ty, off)) <- zip [0 ..] fieldInfos
                        ]

                    _ <- enterNewBlock defLabel $ do
                        panic ("Invalid constructor tag in field accessor for type " ++ typeName)
                        return ()
                    _ <- setNewBlock mergeLabel

                    loadedResult <- saveInstruction (LlvmLoad resultPtr) fieldTy0
                    return $ mkVariableLoad (mkStackStructAlloc fieldTy0 resultPtr) Nothing loadedResult
compileAccessor (TupleElem base elemIdx) args = do
    baseValue <- compileAccessor base args
    let baseType = getGenValueType baseValue

    basePtr <- case baseType of
        LlvmNamedType _ -> do
            stackPtr <- alloca baseType
            tell [LlvmStore baseType (gvw baseValue) stackPtr]
            return stackPtr
        LlvmPointer _ -> return (gvw baseValue)
        _ -> return (gvw baseValue)

    let structType = case baseType of
            LlvmNamedType name -> LlvmNamedType name
            LlvmPointer t -> t
            t -> t

    arrayPtr <-
        saveInstruction
            (LlvmGetElementPtr structType basePtr [intLiteral 0, intLiteral elemIdx] False)
            (LlvmPointer LlvmI8)

    return $ mkStructFieldAccess baseValue elemIdx arrayPtr
compileAccessor (ArrayElem base elemIdx) args = do
    baseValue <- compileAccessor base args

    elemPtr <-
        saveInstruction
            (LlvmGetElementPtr (getGenValueType baseValue) (gvw baseValue) [intLiteral elemIdx] True)
            (LlvmPointer LlvmI8)

    return $ mkArrayElementAccess baseValue (cIntLiteral elemIdx) elemPtr

extractADTTag :: GenValue -> IrGen GenValue
extractADTTag structPtr = do
    let baseType = getGenValueType structPtr

    basePtr <- case baseType of
        LlvmNamedType _ -> do
            stackPtr <- alloca baseType
            tell [LlvmStore baseType (gvw structPtr) stackPtr]
            return stackPtr
        LlvmPointer _ -> return (gvw structPtr)
        _ -> return (gvw structPtr)

    let structType = case baseType of
            LlvmNamedType name -> LlvmNamedType name
            LlvmPointer t -> t
            t -> t

    tagPtr <-
        saveInstruction
            (LlvmGetElementPtr structType basePtr [intLiteral 0, intLiteral 0] False)
            (LlvmPointer LlvmI8)

    tag <- saveInstruction (LlvmLoad tagPtr) LlvmI8
    return $ mkADTTagAccess structPtr tag

compileSwitchBranches :: GenValue -> [(Constructor, String, NodeId)] -> String -> IrGen ()
compileSwitchBranches tag branches defaultLabel = do
    case branches of
        [] -> tell [LlvmBr defaultLabel]
        [(DataCtor ctorName _, label, _)] -> do
            actualTag <- getConstructorTag ctorName
            cmp <-
                saveInstruction
                    (LlvmICmp LlvmI8 "eq" (gvw tag) (byteLiteral actualTag))
                    LlvmI1
            tell [LlvmBrCond cmp label defaultLabel]
        _ -> do
            casesWithTags <- sequence [(\ctorTag -> (byteLiteral ctorTag, label)) <$> getConstructorTag ctorName | (DataCtor ctorName _, label, _) <- branches]
            tell [LlvmSwitch (gvw tag) defaultLabel casesWithTags]

compileLiteralSwitchBranches :: GenValue -> [(Constructor, String, NodeId)] -> String -> IrGen ()
compileLiteralSwitchBranches value branches defaultLabel = do
    case branches of
        [] -> tell [LlvmBr defaultLabel]
        [(LitCtor lit, label, _)] -> do
            cmp <- compareLiteral value lit
            tell [LlvmBrCond cmp label defaultLabel]
        ((LitCtor lit, label, _) : rest) -> do
            cmp <- compareLiteral value lit

            blockNum <- gets nextBlock
            modify $ \s -> s{nextBlock = blockNum + 1}
            currentFn <- asks currentFunction
            let fnPrefix = fromMaybe "match" currentFn
            let nextLabel = fnPrefix ++ ".litcheck." ++ show blockNum

            tell [LlvmBrCond cmp label nextLabel]
            _ <- setNewBlock nextLabel
            compileLiteralSwitchBranches value rest defaultLabel
        _ -> error "Invalid literal constructor in switch branches"

compareLiteral :: GenValue -> Literal -> IrGen LlvmValue
compareLiteral value lit = case lit of
    LitInt n -> do
        let valTy = getGenValueType value
        (lhs, cmpTy) <-
            case valTy of
                LlvmPointer innerTy -> do
                    loaded <- saveInstruction (LlvmLoad (gvw value)) innerTy
                    pure (loaded, innerTy)
                _ -> pure (gvw value, valTy)
        saveInstruction (LlvmICmp cmpTy "eq" lhs (intLiteral (fromInteger n))) LlvmI1
    LitBool b -> do
        let boolVal = if b then "1" else "0"
        (lhs, _cmpTy) <-
            case getGenValueType value of
                LlvmPointer innerTy -> do
                    loaded <- saveInstruction (LlvmLoad (gvw value)) innerTy
                    pure (loaded, innerTy)
                ty -> pure (gvw value, ty)
        saveInstruction (LlvmICmp LlvmI1 "eq" lhs (LlvmLiteral LlvmI1 boolVal)) LlvmI1
    LitString s -> do
        let len = length s
        strPtr <- newStrTemplate s len
        lhsVal <-
            case getGenValueType value of
                LlvmPointer LlvmI8 -> pure (gvw value)
                LlvmPointer innerTy -> saveInstruction (LlvmLoad (gvw value)) innerTy
                _ -> pure (gvw value)
        saveInstruction (LlvmICmp (LlvmPointer LlvmI8) "eq" lhsVal (gvw strPtr)) LlvmI1

bindPatternVariablesForAction :: [[Pattern]] -> Int -> [GenValue] -> MemoryScope -> IrGen MemoryScope
bindPatternVariablesForAction patterns actionIdx args scope = do
    if actionIdx < length patterns
        then do
            let pats = patterns !! actionIdx
            bindings <- concat <$> sequence [bindPatternVars pat arg idx | (pat, arg, idx) <- zip3 pats args [0 ..]]
            let newValues = Map.union (Map.fromList bindings) (blockValues scope)
            return scope{blockValues = newValues}
        else return scope

bindPatternVars :: Pattern -> GenValue -> Int -> IrGen [(String, GenValue)]
bindPatternVars (PVar name) value _ = return [(name, value)]
bindPatternVars (PConstructor ctorName subPats) value _idx = do
    md <- getConstructorInfo ctorName
    let argTypes = constructorMetadataArgs md
        fieldLLVMTypes = constructorMetadataFieldLlvmTypes md
        fieldOffsets = constructorMetadataFieldOffsets md

    concat <$> sequence [bindSubPattern subPat value fieldIdx (argTypes !! fieldIdx) (fieldLLVMTypes !! fieldIdx) (fieldOffsets !! fieldIdx) | (subPat, fieldIdx) <- zip subPats [0 ..]]
  where
    bindSubPattern :: Pattern -> GenValue -> Int -> Type -> LlvmType -> Int -> IrGen [(String, GenValue)]
    bindSubPattern (PVar varName) baseValue _fieldIdx _fieldType llvmFieldType fieldOffset = do
        let baseType = getGenValueType baseValue

        basePtr <- case baseType of
            LlvmNamedType _ -> do
                stackPtr <- alloca baseType
                tell [LlvmStore baseType (gvw baseValue) stackPtr]
                return stackPtr
            LlvmPointer _ -> return (gvw baseValue)
            _ -> return (gvw baseValue)

        let structType = case baseType of
                LlvmNamedType name -> LlvmNamedType name
                LlvmPointer t -> t
                t -> t

        arrayPtr <-
            saveInstruction
                (LlvmGetElementPtr structType basePtr [intLiteral 0, intLiteral 1] False)
                (LlvmPointer LlvmI8)

        fieldOffsetPtr <-
            saveInstruction
                (LlvmGetElementPtr LlvmI8 arrayPtr [intLiteral fieldOffset] False)
                (LlvmPointer LlvmI8)

        typedFieldPtr <-
            saveInstruction
                (LlvmBitcast fieldOffsetPtr (LlvmPointer llvmFieldType))
                (LlvmPointer llvmFieldType)

        loadedField <- saveInstruction (LlvmLoad typedFieldPtr) llvmFieldType

        return [(varName, mkVariableLoad (mkStackStructAlloc llvmFieldType typedFieldPtr) Nothing loadedField)]
    bindSubPattern _ _ _ _ _ _ = return []
bindPatternVars _ _ _ = return []

getConstructorInfo :: String -> IrGen ConstructorMetadata
getConstructorInfo ctorName = do
    st <- gets constructorMap
    case Map.lookup ctorName st of
        Just metadata -> return metadata
        Nothing -> error $ "Constructor not found in metadata: " ++ ctorName

getConstructorTag :: String -> IrGen Int
getConstructorTag ctorName = do
    md <- getConstructorInfo ctorName
    return (constructorMetadataTag md)
