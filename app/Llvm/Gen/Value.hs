{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Llvm.Gen.Value where

import Control.Monad (unless)
import Control.Monad.State (MonadState (..), gets, modify)
import Control.Monad.Writer (MonadWriter (..))
import Data.Hashable (hash)
import Data.List (find)
import qualified Data.Map as Map
import GHC.Base (when)
import Llvm.Dependencies (LinkageType (PrivateLinkage), LlvmDependency (LlvmConstantDependency, constantLinkage, constantName, constantValue))
import Llvm.Gen.Core (IrGen, IrGenState (constructorMap, irDependencies, irStructs, typeMap), lookupMemory, saveInstruction)
import Llvm.Gen.Intrinsics (IntrinsicImpl (intrinsicCodeGen), getIntrinsic)
import Llvm.Gen.Metadata (ConstructorMetadata (..))
import Llvm.Gen.Types (llvmTypeToMonomorphicName, toAllocationLlvmType)
import Llvm.Instructions (LlvmInstruction (..), LlvmStatement (LlvmStore))
import Llvm.Modules (LlvmStruct (LlvmStruct))
import Llvm.Types (LlvmType (..), deref, getLlvmTypeSize)
import Llvm.Values (LlvmValue (..), getValueType, intLiteral)
import Project.Symbols (Symbol (ResolvedSymbol), SymbolKind (..))
import Syntax.Tree (Expr (..), uncurryApp)
import Typing.Currying (uncurryFunction)
import Typing.Types (QualifiedType (Forall), isPolymorphic)

compileValue :: Expr -> IrGen LlvmValue
compileValue expr = case expr of
    ExprNum n _ -> return $ LlvmLiteral LlvmI32 n
    ExprUVar name _ -> do
        maybeMem <- lookupMemory name
        case maybeMem of
            Just mem -> return mem
            Nothing -> error $ "Undefined variable: " ++ name
    ExprStr str _ -> do
        let depName = "str_" ++ show (hash str)
        let depType = LlvmArray (length str + 1) LlvmI8
        let dependency =
                LlvmConstantDependency
                    { constantName = depName
                    , constantValue = LlvmLiteral depType ("c\"" ++ str ++ "\00\"")
                    , constantLinkage = Just PrivateLinkage
                    }
        modify $ \s -> s{irDependencies = dependency : irDependencies s}

        let ptrInstr = LlvmGetElementPtr depType (LlvmGlobal depType depName) [intLiteral 0, intLiteral 0] True
        saveInstruction ptrInstr (LlvmPointer LlvmI8)
    ExprApp fn arg -> do
        if isConstructor fn
            then do
                let (ctorExpr, args) = uncurryApp expr
                let ctorName = getConstructorName ctorExpr

                compileConstructorApp ctorName args
            else do
                tyMap <- gets typeMap
                let (callBase, nestedCallArgs) = uncurryApp fn
                let callArgs = arg : nestedCallArgs
                argVals <- mapM compileValue callArgs
                let Just (Forall _ _ refType) = Map.lookup callBase tyMap
                let (_fnIntermediateTys, fnRetType) = uncurryFunction refType
                let callName = getApplicableFnName callBase
                let llvmFnType = toAllocationLlvmType fnRetType
                call <- case callName of
                    ResolvedSymbol name IntrinsicBindingSymbol _ _ -> do
                        let intrinsic = getIntrinsic name
                        intrinsicCodeGen intrinsic argVals
                    ResolvedSymbol name _ _ _ -> do
                        pure $ LlvmCall (LlvmGlobal LlvmFn name) llvmFnType argVals
                saveInstruction call llvmFnType
    _ -> error $ "Unsupported llvm value expression type: " ++ show expr

compileConstructorApp :: String -> [Expr] -> IrGen LlvmValue
compileConstructorApp ctorName args = do
    ConstructorMetadata baseTypeName tag argTypes <- getConstructorInfo ctorName

    argVals <- mapM compileValue args
    let concreteArgTypes = map getValueType argVals
    let isConstructorPolymorphic = any isPolymorphic argTypes

    let monomorphicName =
            if not isConstructorPolymorphic
                then baseTypeName
                else baseTypeName ++ concatMap (("_" ++) . llvmTypeToMonomorphicName) concreteArgTypes

    let structType = LlvmNamedType monomorphicName
    structPtr <- saveInstruction (LlvmAlloca structType) (LlvmPointer structType)
    writeTag structPtr tag
    when isConstructorPolymorphic $ do
        ensureMonomorphicStructExists monomorphicName concreteArgTypes
        dataPtr <- getUnionDataPtr structPtr monomorphicName
        writeConstructorData dataPtr args
    return structPtr

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

getUnionDataPtr :: LlvmValue -> String -> IrGen LlvmValue
getUnionDataPtr structPtr typeName = do
    let structType = LlvmNamedType typeName
    st <- get
    let Just structDef = find (\(LlvmStruct name _) -> name == typeName) (irStructs st)
    let LlvmStruct _ fields = structDef
    let arrayType = fields !! 1

    saveInstruction
        (LlvmGetElementPtr structType structPtr [intLiteral 0, intLiteral 1] False)
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

isConstructor :: Expr -> Bool
isConstructor (ExprVar (ResolvedSymbol _ (DataConstructorSymbol{}) _ _) _) = True
isConstructor _ = False

getConstructorName :: Expr -> String
getConstructorName (ExprVar (ResolvedSymbol name _ _ _) _) = name
getConstructorName _ = error "Not a constructor"

writeConstructorData :: LlvmValue -> [Expr] -> IrGen ()
writeConstructorData dataPtr args = do
    writeFieldsSequentially dataPtr args 0

writeFieldsSequentially :: LlvmValue -> [Expr] -> Int -> IrGen ()
writeFieldsSequentially _ [] _ = return ()
writeFieldsSequentially dataPtr (arg : rest) offset = do
    argVal <- compileValue arg
    let argType = getValueType argVal

    fieldPtr <- getFieldPtrAtOffset dataPtr offset

    typedPtr <-
        saveInstruction
            (LlvmBitcast fieldPtr (LlvmPointer argType))
            (LlvmPointer argType)

    tell [LlvmStore argType argVal typedPtr]

    let fieldSize = getLlvmTypeSize argType
    writeFieldsSequentially dataPtr rest (offset + fieldSize)

getFieldPtrAtOffset :: LlvmValue -> Int -> IrGen LlvmValue
getFieldPtrAtOffset dataPtr offset = do
    saveInstruction
        ( LlvmGetElementPtr
            (deref $ getValueType dataPtr)
            dataPtr
            [intLiteral 0, intLiteral offset]
            False
        )
        (LlvmPointer LlvmI8)
