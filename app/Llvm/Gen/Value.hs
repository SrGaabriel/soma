{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Llvm.Gen.Value where

import Control.Monad (unless)
import Control.Monad.Reader (ReaderT)
import Control.Monad.State (MonadState (..), State, gets)
import Control.Monad.Writer (MonadWriter (..), WriterT)
import qualified Data.Map as Map
import Llvm.Gen.Core (IrGen, IrGenEnv, IrGenState (constructorMap, typeMap, irStructs), lookupMemory, saveInstruction)
import Llvm.Gen.Metadata (ConstructorMetadata (..))
import Llvm.Gen.Types (toAllocationLlvmType)
import Llvm.Instructions (LlvmInstruction (..), LlvmStatement (LlvmStore))
import Llvm.Intrinsics (IntrinsicImpl (intrinsicCodeGen), getIntrinsic)
import Llvm.Types (LlvmType (..), getLlvmTypeSize, deref)
import Llvm.Values (LlvmValue (..), getValueType, intLiteral)
import Project.Symbols (Symbol (ResolvedSymbol), SymbolKind (..), resolvedSymbolKind)
import Syntax.Tree (Expr (..), uncurryApp)
import Typing.Currying (uncurryFunction)
import Typing.Types (QualifiedType (Forall))
import Llvm.Modules (LlvmStruct(LlvmStruct))
import Data.List (find)

compileValue :: Expr -> IrGen LlvmValue
compileValue expr = case expr of
    ExprNum n _ -> return $ LlvmLiteral LlvmI32 n
    ExprUVar name _ -> do
        maybeMem <- lookupMemory name
        case maybeMem of
            Just mem -> return mem
            Nothing -> error $ "Undefined variable: " ++ name
    ExprApp fn arg -> do
        if isConstructor fn
            then do
                let (ctorExpr, args) = uncurryApp expr
                let ctorName = getConstructorName ctorExpr

                compileConstructorApp ctorName args
            else do
                -- Regular function call
                tyMap <- gets typeMap
                let (callBase, nestedCallArgs) = uncurryApp fn
                let callArgs = arg : nestedCallArgs
                argVals <- mapM compileValue callArgs
                let Just (Forall _ _ refType) = Map.lookup callBase tyMap
                let (_fnIntermediateTys, fnRetType) = uncurryFunction refType
                let callName = getApplicableFnName callBase
                let llvmFnType = toAllocationLlvmType fnRetType
                let call = case callName of
                        ResolvedSymbol name IntrinsicBindingSymbol _ _ -> do
                            let intrinsic = getIntrinsic name
                            intrinsicCodeGen intrinsic argVals
                        ResolvedSymbol name _ _ _ -> do
                            LlvmCall (LlvmGlobal LlvmFn name) llvmFnType argVals
                saveInstruction call llvmFnType
    _ -> error $ "Unsupported llvm value expression type: " ++ show expr

compileConstructorApp :: String -> [Expr] -> IrGen LlvmValue
compileConstructorApp ctorName args = do
    ConstructorMetadata typeName tag _ <- getConstructorInfo ctorName

    let structType = LlvmNamedType typeName
    structPtr <- saveInstruction (LlvmAlloca structType) (LlvmPointer structType)

    writeTag structPtr tag

    unless (null args) $ do
        dataPtr <- getUnionDataPtr structPtr typeName
        writeConstructorData dataPtr args

    return structPtr

getUnionDataPtr :: LlvmValue -> String -> IrGen LlvmValue
getUnionDataPtr structPtr typeName = do
    let structType = LlvmNamedType typeName
    st <- get
    let Just structDef = find (\(LlvmStruct name _) -> name == typeName) (irStructs st)
    let LlvmStruct _ fields = structDef
    let arrayType = fields !! 1

    saveInstruction
        (LlvmGetElementPtr structType structPtr [intLiteral 0, intLiteral 1])
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
            (LlvmGetElementPtr (deref $ getValueType structPtr) structPtr [intLiteral 0, intLiteral 0])
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
        )
        (LlvmPointer LlvmI8)
