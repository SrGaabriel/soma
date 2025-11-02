{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Llvm.Gen.Value where

import Control.Monad (unless)
import Control.Monad.Reader (MonadReader (ask), ReaderT (..), asks)
import Control.Monad.State (MonadState (..), gets, modify, runState)
import Control.Monad.Writer (MonadWriter (..), WriterT (..))
import Data.Foldable (forM_)
import Data.List (find)
import qualified Data.Map as Map
import GHC.Base (when)
import Llvm.Dependencies (LlvmDependency (LlvmStructDependency))
import Llvm.Gen.Arrays (createSlice, createTypedRefCountedHeapArray, storeArrayElement)
import Llvm.Gen.Calls (mkTypeclassMethodCall)
import Llvm.Gen.Context
import Llvm.Gen.Core (IrGen, IrGenEnv (..), IrGenState (constructorMap, irDependencies, polymorphicFunctions, typeMap), MemoryScope (..), coerceArgsForCall, freshScope, lookupMemory, mkFnCall, saveInstruction)
import Llvm.Gen.Externals (importExternalDependency)
import Llvm.Gen.Functions (compileFunction)
import Llvm.Gen.Intrinsics (IntrinsicImpl (intrinsicCodeGen), getIntrinsic)
import Llvm.Gen.Mangling (mangleDataTypeName, mangleMonomorphizedName)
import Llvm.Gen.Metadata (ConstructorMetadata (..))
import Llvm.Gen.Monomorphize (monomorphizeAndCompile)
import Llvm.Gen.Templates (newStrTemplate)
import Llvm.Gen.Types (getArrayElementType, toAllocationLlvmType)
import Llvm.Instructions (LlvmInstruction (..), LlvmStatement (LlvmStore))
import Llvm.Types (LlvmType (..), deref, getLlvmTypeSize)
import Llvm.Values (LlvmValue (..), getValueType, intLiteral)
import Project.Symbols (Symbol (..), SymbolKind (..))
import Syntax.Tree (Expr (..), uncurryApp)
import Typing.Currying (uncurryFunction)
import Typing.Types (Constraint (..), QualifiedType (Forall), Type (..), constraintClassName, constraintTypes, isPolymorphic)
import Utils.Lists (hardHead)

compileValue :: Expr -> IrGen GenValue
compileValue expr = case expr of
    ExprNum n _ -> return $ Contextualized (LiteralValue NumLit) (LlvmLiteral LlvmI32 n)
    ExprBool b _ -> return $ Contextualized (LiteralValue BoolLit) (LlvmLiteral LlvmI1 (if b then "1" else "0"))
    ExprUVar name _ -> do
        maybeMem <- lookupMemory name
        case maybeMem of
            Just mem -> return mem
            Nothing -> error $ "Undefined variable: " ++ name
    ExprVar s@(ResolvedSymbol{resolvedSymbolName, resolvedSymbolKind, resolvedSymbolPackage}) _ -> do
        packageName <- asks currentPackage
        when (resolvedSymbolPackage /= packageName) $ importExternalDependency s

        case resolvedSymbolKind of
            BindingSymbol bindingTyp -> do
                compileApp expr [] bindingTyp
            _ -> do
                maybeMem <- lookupMemory resolvedSymbolName
                case maybeMem of
                    Just mem -> return mem
                    Nothing -> error $ "Undefined variable: " ++ resolvedSymbolName
    ExprArray elements _ -> compileArrayLiteral expr elements
    ExprStr str _ -> newStrTemplate str (length str)
    ExprLet name valueExpr bodyExpr _ -> do
        compiledValue <- compileValue valueExpr
        newScope <- freshScope name
        let updatedScope = newScope{blockValues = Map.singleton name compiledValue}
        env <- ask
        let newEnv = env{currentScope = updatedScope}
        st <- get
        let ((returningValue, stmts), st') = runState (runWriterT (runReaderT (compileValue bodyExpr) newEnv)) st
        put st'
        tell stmts
        return returningValue
    ExprLambda{} -> do
        let fnName = "lambda" -- todo: mangle name
        tyEnv <- gets typeMap
        let Just (Forall _ _ fnType) = Map.lookup expr tyEnv
        compileFunction fnName fnType expr compileValue

        let (argTypes, retType) = uncurryFunction fnType
        let llvmFnType = toAllocationLlvmType retType
        let llvmArgTypes = map toAllocationLlvmType argTypes
        let fnPointerTyp = LlvmPointer $ LlvmFn llvmFnType llvmArgTypes
        funcPtr <- saveInstruction (LlvmAlloca fnPointerTyp Nothing) (LlvmPointer fnPointerTyp)
        tell [LlvmStore fnPointerTyp (LlvmGlobal fnPointerTyp "lambda") funcPtr]
        loaded <- saveInstruction (LlvmLoad funcPtr) fnPointerTyp
        pure $ mkLambdaPtrLoad (mkLambdaPtrAlloc fnName funcPtr) loaded
    ExprApp _ _ -> do
        let (base, args) = uncurryApp expr
        tyEnv <- gets typeMap
        let Just qualifiedType = Map.lookup base tyEnv
        compileApp base args qualifiedType
    _ -> error $ "Unsupported llvm value expression type: " ++ show expr

compileApp :: Expr -> [Expr] -> QualifiedType -> IrGen GenValue
compileApp base args (Forall _ _ methodType) = do
    case base of
        ExprVar symbol@(ResolvedSymbol{resolvedSymbolName}) _ | isDataConstructor symbol -> do
            compileConstructorApp resolvedSymbolName args
        ExprVar symbol@(ResolvedSymbol{resolvedSymbolName}) _ | isTypeclassMethod symbol -> do
            let TypeClassMethodSymbol className = resolvedSymbolKind symbol
            argVals <- mapM compileValue args
            let (paramTypes, retType) = uncurryFunction methodType
            let llvmParamTypes = map toAllocationLlvmType paramTypes
            mkTypeclassMethodCall className resolvedSymbolName argVals llvmParamTypes (toAllocationLlvmType retType)
        ExprUVar _ _ -> do
            basePtr <- compileValue base
            argVals <- mapM compileValue args
            let (_paramTypes, retType) = uncurryFunction methodType
            let llvmRetType = toAllocationLlvmType retType
            Contextualized (FunctionCall $ IndirectCall basePtr argVals llvmRetType)
                <$> saveInstruction (LlvmCall (gvw basePtr) llvmRetType (map gvw argVals)) llvmRetType
        _ -> do
            tyMap <- gets typeMap
            argVals <- mapM compileValue args
            let Just (Forall _ _ refType) = Map.lookup base tyMap
            let (fnParamTys, fnRetType) = uncurryFunction refType
            let callName = getApplicableFnName base
            let llvmFnType = toAllocationLlvmType fnRetType
            let llvmParamTypes = map toAllocationLlvmType fnParamTys
            coercedArgVals <- coerceArgsForCall argVals llvmParamTypes
            call <- case callName of
                ResolvedSymbol name IntrinsicBindingSymbol _ _ _ -> do
                    let intrinsic = getIntrinsic name
                    intrinsicCodeGen intrinsic coercedArgVals
                ResolvedSymbol name (BindingSymbol _) _ packageName _ -> do
                    currentPckg <- asks currentPackage
                    polyFuncs <- gets polymorphicFunctions
                    when (packageName /= currentPckg) $ importExternalDependency callName
                    case Map.lookup name polyFuncs of
                        Just _ -> do
                            let argTypes =
                                    map
                                        ( \arg ->
                                            let Just (Forall _ _ typ) = Map.lookup arg tyMap
                                            in typ
                                        )
                                        args
                            mangledName <- monomorphizeAndCompile name argTypes compileValue
                            pure $ mkFnCall mangledName coercedArgVals llvmFnType
                        Nothing -> do
                            pure $ mkFnCall name coercedArgVals llvmFnType
                ResolvedSymbol name _ _ _ _ -> do
                    pure $ mkFnCall name coercedArgVals llvmFnType
            callResult <- saveInstruction call llvmFnType
            let callFnName = case callName of
                    ResolvedSymbol name _ _ _ _ -> name
            return $ mkDirectCall callFnName coercedArgVals (toAllocationLlvmType fnRetType) callResult

compileConstructorApp :: String -> [Expr] -> IrGen GenValue
compileConstructorApp ctorName args = do
    ConstructorMetadata{constructorMetadataTypeName = baseTypeName, constructorMetadataTag = tag, constructorMetadataArgs = argTypes} <- getConstructorInfo ctorName

    argVals <- mapM compileValue args
    let concreteArgTypes = map getGenValueType argVals
    let isConstructorPolymorphic = any isPolymorphic argTypes

    let monomorphicName =
            if isConstructorPolymorphic
                then
                    mangleMonomorphizedName baseTypeName concreteArgTypes
                else
                    mangleDataTypeName baseTypeName
    let structType = LlvmNamedType monomorphicName
    structPtr <- saveInstruction (LlvmAlloca structType Nothing) (LlvmPointer structType)
    writeTag structPtr tag
    let cStructPtr = mkStackStructAlloc structType structPtr
    when isConstructorPolymorphic $ do
        ensureMonomorphicStructExists monomorphicName concreteArgTypes
        dataPtr <- getUnionDataPtr cStructPtr monomorphicName
        writeConstructorData dataPtr args
    return cStructPtr

ensureMonomorphicStructExists :: String -> [LlvmType] -> IrGen ()
ensureMonomorphicStructExists monomorphicName concreteArgTypes = do
    st <- get
    let exists =
            any
                ( \case
                    (LlvmStructDependency name _) -> name == monomorphicName
                    _ -> False
                )
                (irDependencies st)

    unless exists $ do
        let variantSizes = map getLlvmTypeSize concreteArgTypes
        let maxSize = if null variantSizes then 0 else maximum variantSizes
        let fields = [LlvmI8, LlvmArray maxSize LlvmI8]
        let structDef = LlvmStructDependency monomorphicName fields

        modify $ \s -> s{irDependencies = structDef : irDependencies s}

getUnionDataPtr :: GenValue -> String -> IrGen GenValue
getUnionDataPtr structPtr typeName = do
    let structType = LlvmNamedType typeName
    st <- get
    let Just (LlvmStructDependency _ fields) =
            find
                ( \case
                    (LlvmStructDependency name _) -> name == typeName
                    _ -> False
                )
                (irDependencies st)
    let arrayType = fields !! 1

    mkADTUnionDataAccess structPtr
        <$> saveInstruction
            (LlvmGetElementPtr structType (gvw structPtr) [intLiteral 0, intLiteral 1] False)
            (LlvmPointer arrayType)

getConstructorInfo :: String -> IrGen ConstructorMetadata
getConstructorInfo ctorName = do
    st <- get
    case Map.lookup ctorName (constructorMap st) of
        Just metadata -> return metadata
        Nothing -> error $ "Constructor not found in metadata: " ++ ctorName

writeTag :: LlvmValue -> Int -> IrGen ()
writeTag structPtr t = do
    tagPtr <-
        saveInstruction
            (LlvmGetElementPtr (deref $ getValueType structPtr) structPtr [intLiteral 0, intLiteral 0] False)
            (LlvmPointer LlvmI8)

    tell [LlvmStore LlvmI8 (intLiteral t) tagPtr]

getApplicableFnName :: Expr -> Symbol
getApplicableFnName (ExprVar r@(ResolvedSymbol{}) _) = r
getApplicableFnName u = error $ "Cannot get function name from expression: " ++ show u

isDataConstructor :: Symbol -> Bool
isDataConstructor symbol = case resolvedSymbolKind symbol of
    DataConstructorSymbol _ -> True
    _ -> False

isTypeclassMethod :: Symbol -> Bool
isTypeclassMethod symbol = case resolvedSymbolKind symbol of
    TypeClassMethodSymbol _ -> True
    _ -> False

getConstructorName :: Expr -> String
getConstructorName (ExprVar (ResolvedSymbol name _ _ _ _) _) = name
getConstructorName _ = error "Not a constructor"

writeConstructorData :: GenValue -> [Expr] -> IrGen ()
writeConstructorData dataPtr args = do
    writeFieldsSequentially dataPtr args 0

writeFieldsSequentially :: GenValue -> [Expr] -> Int -> IrGen ()
writeFieldsSequentially _ [] _ = return ()
writeFieldsSequentially dataPtr (arg : rest) offset = do
    argVal <- compileValue arg
    let argType = getGenValueType argVal

    fieldPtr <- getFieldPtrAtOffset dataPtr offset

    typedPtr <-
        saveInstruction
            (LlvmBitcast fieldPtr (LlvmPointer argType))
            (LlvmPointer argType)

    tell [LlvmStore argType (gvw argVal) typedPtr]

    let fieldSize = getLlvmTypeSize argType
    writeFieldsSequentially dataPtr rest (offset + fieldSize)

getFieldPtrAtOffset :: GenValue -> Int -> IrGen LlvmValue
getFieldPtrAtOffset dataPtr offset = do
    saveInstruction
        ( LlvmGetElementPtr
            (deref $ getGenValueType dataPtr)
            (gvw dataPtr)
            [intLiteral 0, intLiteral offset]
            False
        )
        (LlvmPointer LlvmI8)

extractConcreteTypeFromConstraint :: [Constraint] -> String -> Type
extractConcreteTypeFromConstraint constraints className =
    case find (\c -> constraintClassName c == className) constraints of
        Just constraint -> case constraintTypes constraint of
            [concreteType] -> concreteType
            types -> hardHead types
        Nothing -> error $ "Constraint not found for class: " ++ className ++ " in: " ++ show constraints

compileArrayLiteral :: Expr -> [Expr] -> IrGen GenValue
compileArrayLiteral arrayExpr elements = do
    when (null elements)
        $ error "Empty arrays not yet supported"
    let len = length elements

    tyMap <- gets typeMap
    let arrayType = case Map.lookup arrayExpr tyMap of
            Just (Forall _ _ ty) -> ty
            Nothing -> error $ "Array expression not in type map: " ++ show arrayExpr

    let elemType = getArrayElementType arrayType
    let llvmElemType = toAllocationLlvmType elemType

    arrayPtr <- createTypedRefCountedHeapArray llvmElemType len

    compiledElems <- mapM compileValue elements
    forM_ (zip [0 ..] compiledElems) $ \(idx, elemValue) -> do
        storeArrayElement arrayPtr (cLongLiteral idx) elemValue llvmElemType

    createSlice arrayPtr len
