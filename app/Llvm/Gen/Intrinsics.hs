{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Llvm.Gen.Intrinsics where

import Control.Monad.State (modify)
import Control.Monad.Writer (tell)
import Llvm.Dependencies (LlvmDependency (..))
import Llvm.Gen.Arrays (createTypedDynamicSizedRefCountedHeapArray, extractSliceLen, loadArrayElement)
import Llvm.Gen.Calls (mkTypeclassMethodCall)
import Llvm.Gen.Context (ArrayOpCtx (..), FunctionCallCtx (..), GenCtx (..), GenValue (..), MemAccessCtx (..), getGenValueType, mkIterationIndexAlloc, mkVariableLoad)
import Llvm.Gen.Core (IrGen, IrGenState (irDependencies), alloca, enterNewBlock, mkFnCall, saveInstruction, setNewBlock)
import Llvm.Gen.Templates (newStrTemplate)
import Llvm.Instructions (LlvmInstruction (..), LlvmStatement (..))
import Llvm.Types (LlvmType (..))
import Llvm.Values (LlvmValue (..), intLiteral)

data IntrinsicImpl = IntrinsicImpl
    { intrinsicName :: String
    , intrinsicCodeGen :: [GenValue] -> IrGen LlvmInstruction
    }

addIntIntrinsic :: IntrinsicImpl
addIntIntrinsic =
    IntrinsicImpl
        { intrinsicName = "+"
        , intrinsicCodeGen = \case
            [lhs, rhs] ->
                let lhsType = getGenValueType lhs
                in pure $ LlvmAdd lhsType (gvw lhs) (gvw rhs)
            _ -> error "add_int intrinsic expects exactly 2 arguments"
        }

eqIntIntrinsic :: IntrinsicImpl
eqIntIntrinsic =
    IntrinsicImpl
        { intrinsicName = "=="
        , intrinsicCodeGen = \case
            [lhs, rhs] ->
                let lhsType = getGenValueType lhs
                in pure $ LlvmICmp lhsType "eq" (gvw lhs) (gvw rhs)
            _ -> error "eq_int intrinsic expects exactly 2 arguments"
        }

printIntrinsic :: IntrinsicImpl
printIntrinsic =
    IntrinsicImpl
        { intrinsicName = "print"
        , intrinsicCodeGen = \case
            [arg] -> do
                modify $ \state -> state{irDependencies = printfDependency : irDependencies state}
                pure $ mkFnCall "printf" [arg] LlvmI32
            _ -> error "print intrinsic expects exactly 1 argument"
        }

printlnIntrinsic :: IntrinsicImpl
printlnIntrinsic =
    IntrinsicImpl
        { intrinsicName = "println"
        , intrinsicCodeGen = \case
            [arg] -> do
                case getGenValueType arg of
                    LlvmPointer LlvmI8 -> do
                        modify $ \state -> state{irDependencies = putsDependency : irDependencies state}
                        pure $ mkFnCall "puts" [arg] LlvmI32
                    LlvmI32 -> do
                        formatStr <- newStrTemplate "%d\\0A" 3
                        modify $ \state -> state{irDependencies = printfDependency : irDependencies state}
                        pure $ mkFnCall "printf" [formatStr, arg] LlvmI32
                    _ -> do
                        displayFn <- mkTypeclassMethodCall "Display" "display" [arg] (LlvmPointer LlvmI8)
                        modify $ \state -> state{irDependencies = putsDependency : irDependencies state}
                        pure $ mkFnCall "puts" [displayFn] LlvmI32
            _ -> error "println intrinsic expects exactly 1 argument"
        }

debugIntrinsic :: IntrinsicImpl
debugIntrinsic =
    IntrinsicImpl
        { intrinsicName = "debug"
        , intrinsicCodeGen = \case
            [arg] -> do
                modify $ \state -> state{irDependencies = putsDependency : irDependencies state}
                pure $ mkFnCall "puts" [arg] LlvmI32
            _ -> error "debug intrinsic expects exactly 1 argument"
        }

mapIntrinsic :: IntrinsicImpl
mapIntrinsic =
    IntrinsicImpl
        { intrinsicName = "map"
        , intrinsicCodeGen = \case
            [lambda, array] -> do
                index <- alloca LlvmI32 -- todo: use phi nodes
                let ctxIndex = mkIterationIndexAlloc index
                tell [LlvmStore LlvmI32 (intLiteral 0) index]

                let (LlvmPointer (LlvmFn fnRetType _)) = getGenValueType lambda
                arrayLen <- extractSliceLen array
                let elemType = case genValueContext array of
                        MemoryAccess (ArrayHeaderOffset _ elType) -> elType
                        FunctionCall (DirectCall _ _ elType) -> elType
                        u -> error $ "map intrinsic received unsupported array gen value context: " ++ show u
                newArray <- createTypedDynamicSizedRefCountedHeapArray fnRetType arrayLen -- todo: not make this heap allocated
                tell [LlvmBr "map.cond"]
                _ <-
                    enterNewBlock
                        -- todo: mangle name
                        "map.cond"
                        ( do
                            loadedIndex <- saveInstruction (LlvmLoad index) LlvmI32
                            cmp <- saveInstruction (LlvmICmp LlvmI32 "slt" loadedIndex (gvw arrayLen)) LlvmI1
                            tell [LlvmBrCond cmp "map.body" "map.end"]
                        )
                _ <-
                    enterNewBlock
                        "map.body"
                        ( do
                            loadedIndex <- mkVariableLoad ctxIndex Nothing <$> saveInstruction (LlvmLoad index) LlvmI32
                            element <- loadArrayElement array loadedIndex elemType
                            mappedElement <- saveInstruction (LlvmCall (gvw lambda) fnRetType [gvw element]) fnRetType
                            newElementPtr <- saveInstruction (LlvmGetElementPtr fnRetType (gvw newArray) [gvw loadedIndex] True) fnRetType
                            tell [LlvmStore fnRetType mappedElement newElementPtr]
                            incrementedIndex <- saveInstruction (LlvmAdd LlvmI32 (gvw loadedIndex) (intLiteral 1)) LlvmI32
                            tell [LlvmStore LlvmI32 incrementedIndex index]
                            tell [LlvmBr "map.cond"]
                        )
                _ <- setNewBlock "map.end"
                let arrayStructType = LlvmAnonymous [LlvmPointer elemType, LlvmI32]
                undefStruct <- saveInstruction (LlvmInsertValue arrayStructType LlvmUndef (gvw newArray) 0) arrayStructType
                pure $ LlvmInsertValue arrayStructType undefStruct (gvw arrayLen) 1
            _ -> error "map intrinsic expects exactly 2 arguments"
        }

getIntrinsic :: String -> IntrinsicImpl
getIntrinsic "==" = eqIntIntrinsic
getIntrinsic "+" = addIntIntrinsic
getIntrinsic "print" = printIntrinsic
getIntrinsic "println" = printlnIntrinsic
getIntrinsic "map" = mapIntrinsic
getIntrinsic u = error $ "Unknown intrinsic function: " ++ u

printfDependency :: LlvmDependency
printfDependency = LlvmFunctionDependency "printf" LlvmI32 [LlvmPointer LlvmI8, LlvmVararg]

putsDependency :: LlvmDependency
putsDependency = LlvmFunctionDependency "puts" LlvmI32 [LlvmPointer LlvmI8]
