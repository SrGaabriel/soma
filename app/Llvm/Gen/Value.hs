{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Llvm.Gen.Value where

import Control.Monad (unless)
import Control.Monad.Reader (MonadReader (ask), ReaderT (..))
import Control.Monad.State (MonadState (..), gets, modify, runState)
import Control.Monad.Writer (MonadWriter (..), WriterT (..))
import Data.Foldable (forM_)
import Data.List (find)
import qualified Data.Map as Map
import GHC.Base (when)
import Llvm.Gen.Arrays (createSlice, createTypedRefCountedHeapArray, storeArrayElement)
import Llvm.Gen.Context
import Llvm.Gen.Core (IrGen, IrGenEnv (..), IrGenState (constructorMap, irStructs, polymorphicFunctions, typeMap), MemoryScope (..), freshScope, lookupMemory, saveInstruction)
import Llvm.Gen.Intrinsics (IntrinsicImpl (intrinsicCodeGen), getIntrinsic)
import Llvm.Gen.Mangling (mangleInstanceMethod)
import Llvm.Gen.Metadata (ConstructorMetadata (..))
import Llvm.Gen.Monomorphize (monomorphizeAndCompile)
import Llvm.Gen.Templates (newStrTemplate)
import Llvm.Gen.Types (getArrayElementType, llvmTypeToMonomorphicName, toAllocationLlvmType)
import Llvm.Instructions (LlvmInstruction (..), LlvmStatement (LlvmStore))
import Llvm.Modules (LlvmStruct (LlvmStruct))
import Llvm.Types (LlvmType (..), deref, getLlvmTypeSize)
import Llvm.Values (LlvmValue (..), getValueType, intLiteral)
import Project.Symbols (Symbol (ResolvedSymbol, resolvedSymbolKind, resolvedSymbolName), SymbolKind (..))
import Syntax.Tree (Expr (..), uncurryApp)
import Typing.Currying (uncurryFunction)
import Typing.Types (Constraint (..), Kind (..), QualifiedType (Forall), TyConstructor (..), Type (..), constraintClassName, constraintTypes, isPolymorphic)
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
    ExprArray elements _ -> compileArrayLiteral expr elements
    ExprStr str _ -> Contextualized (LiteralValue StringLit) <$> newStrTemplate str (length str)
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
    ExprApp fn arg -> do
        let (base, allArgs) = uncurryApp expr
        case base of
            ExprVar symbol@(ResolvedSymbol{resolvedSymbolName}) _ | isDataConstructor symbol -> do
                compileConstructorApp resolvedSymbolName allArgs
            ExprVar symbol@(ResolvedSymbol{resolvedSymbolName}) _ | isTypeclassMethod symbol -> do
                let TypeClassMethodSymbol className = resolvedSymbolKind symbol

                argVals <- mapM compileValue allArgs

                let concreteType = case argVals of
                        (firstArg : _) -> llvmTypeToType (getGenValueType firstArg)
                        [] -> error $ "No arguments in typeclass method: " ++ resolvedSymbolName

                let mangledName = mangleInstanceMethod className concreteType resolvedSymbolName

                tyMap <- gets typeMap
                let Just (Forall _ _ methodType) = Map.lookup expr tyMap
                let (_argTypes, retType) = uncurryFunction methodType
                let llvmRetType = toAllocationLlvmType retType

                let rawArgs = map gvw argVals
                mkDirectCall mangledName argVals
                    <$> saveInstruction
                        (LlvmCall (LlvmGlobal LlvmFn mangledName) llvmRetType rawArgs)
                        llvmRetType
            _ -> do
                tyMap <- gets typeMap
                let (callBase, nestedCallArgs) = uncurryApp fn
                let callArgs = arg : nestedCallArgs
                argVals <- mapM compileValue callArgs
                let Just (Forall _ _ refType) = Map.lookup callBase tyMap
                let (_fnIntermediateTys, fnRetType) = uncurryFunction refType
                let callName = getApplicableFnName callBase
                let llvmFnType = toAllocationLlvmType fnRetType
                let argValsRaw = map gvw argVals
                call <- case callName of
                    ResolvedSymbol name IntrinsicBindingSymbol _ _ -> do
                        let intrinsic = getIntrinsic name
                        intrinsicCodeGen intrinsic argVals
                    ResolvedSymbol name BindingSymbol _ _ -> do
                        polyFuncs <- gets polymorphicFunctions
                        case Map.lookup name polyFuncs of
                            Just _ -> do
                                let concreteTypes = map (llvmTypeToType . getValueType) argValsRaw
                                mangledName <- monomorphizeAndCompile name concreteTypes compileValue
                                pure $ LlvmCall (LlvmGlobal LlvmFn mangledName) llvmFnType argValsRaw
                            Nothing -> do
                                pure $ LlvmCall (LlvmGlobal LlvmFn name) llvmFnType argValsRaw
                    ResolvedSymbol name _ _ _ -> do
                        pure $ LlvmCall (LlvmGlobal LlvmFn name) llvmFnType argValsRaw
                callResult <- saveInstruction call llvmFnType
                let callFnName = case callName of
                        ResolvedSymbol name _ _ _ -> name
                return $ mkDirectCall callFnName argVals callResult
    _ -> error $ "Unsupported llvm value expression type: " ++ show expr

compileConstructorApp :: String -> [Expr] -> IrGen GenValue
compileConstructorApp ctorName args = do
    ConstructorMetadata baseTypeName tag argTypes <- getConstructorInfo ctorName

    argVals <- mapM compileValue args
    let concreteArgTypes = map getGenValueType argVals
    let isConstructorPolymorphic = any isPolymorphic argTypes

    let monomorphicName =
            if not isConstructorPolymorphic
                then baseTypeName
                else baseTypeName ++ concatMap (("_" ++) . llvmTypeToMonomorphicName) concreteArgTypes

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
    let exists = any (\(LlvmStruct name _) -> name == monomorphicName) (irStructs st)

    unless exists $ do
        let variantSizes = map getLlvmTypeSize concreteArgTypes
        let maxSize = if null variantSizes then 0 else maximum variantSizes
        let fields = [LlvmI8, LlvmArray maxSize LlvmI8]
        let structDef = LlvmStruct monomorphicName fields

        modify $ \s -> s{irStructs = structDef : irStructs s}

getUnionDataPtr :: GenValue -> String -> IrGen GenValue
getUnionDataPtr structPtr typeName = do
    let structType = LlvmNamedType typeName
    st <- get
    let Just structDef = find (\(LlvmStruct name _) -> name == typeName) (irStructs st)
    let LlvmStruct _ fields = structDef
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
getApplicableFnName u = error (show u)

isDataConstructor :: Symbol -> Bool
isDataConstructor symbol = case resolvedSymbolKind symbol of
    DataConstructorSymbol _ -> True
    _ -> False

isTypeclassMethod :: Symbol -> Bool
isTypeclassMethod symbol = case resolvedSymbolKind symbol of
    TypeClassMethodSymbol _ -> True
    _ -> False

getConstructorName :: Expr -> String
getConstructorName (ExprVar (ResolvedSymbol name _ _ _) _) = name
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

    -- todo: don't heap allocate all arrays
    arrayPtr <- createTypedRefCountedHeapArray llvmElemType len

    compiledElems <- mapM compileValue elements
    forM_ (zip [0 ..] compiledElems) $ \(idx, elemValue) -> do
        storeArrayElement arrayPtr (cLongLiteral idx) elemValue llvmElemType

    createSlice arrayPtr len

llvmTypeToType :: LlvmType -> Type
llvmTypeToType (LlvmNamedType name) = TConstructor (TypeConstructor name KindStar)
llvmTypeToType LlvmI32 = TConstructor (TypeConstructor "Int" KindStar)
llvmTypeToType LlvmI1 = TConstructor (TypeConstructor "Bool" KindStar)
llvmTypeToType LlvmFloat = TConstructor (TypeConstructor "Float" KindStar)
llvmTypeToType (LlvmPointer inner) = llvmTypeToType inner
llvmTypeToType t = error $ "Cannot convert LLVM type to Type: " ++ show t
