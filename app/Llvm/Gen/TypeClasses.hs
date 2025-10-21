{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Llvm.Gen.TypeClasses where

import Control.Monad.State (modify)
import qualified Data.Map as Map
import Llvm.Gen.Core
import Llvm.Gen.Functions (compileFunction)
import Llvm.Gen.Mangling (extractConstraintParts, mangleInstanceMethod)
import Llvm.Gen.Metadata (InstanceMetadata (..), TypeClassMetadata (..))
import Llvm.Gen.Value (compileValue)
import Llvm.Instructions (LlvmInstruction (..))
import Llvm.Types (LlvmType (..))
import Llvm.Values (LlvmValue, getValueType, intLiteral)
import Syntax.Tree (Expr (ExprBindingDef, ExprInstanceDef, ExprTypeClassBinding, ExprTypeClassDef))
import Typing.Types (QualifiedType (..), Type (..))

compileTypeClassDef :: Expr -> IrGen ()
compileTypeClassDef (ExprTypeClassDef className generics bindings _span) = do
    let methods = Map.fromList $ map extractMethodSignature bindings

    let tcInfo =
            TypeClassMetadata
                { tcName = className
                , tcTypeVars = generics
                , tcMethods = methods
                }

    modify $ \s -> s{typeclasses = tcInfo : typeclasses s}
compileTypeClassDef _ = error "Expected ExprTypeClassDef"

extractMethodSignature :: Expr -> (String, QualifiedType)
extractMethodSignature (ExprTypeClassBinding methodName methodType _defaultImpl _span) =
    (methodName, methodType)
extractMethodSignature _ = error "Expected ExprTypeClassBinding"

compileInstanceDef :: Expr -> IrGen ()
compileInstanceDef (ExprInstanceDef constraintType methods _span) = do
    let (className, concreteType) = extractConstraintParts constraintType
    let instInfo =
            InstanceMetadata
                { instClassName = className
                , instType = concreteType
                }
    modify $ \s -> s{instances = instInfo : instances s}

    mapM_ (compileInstanceMethod className concreteType) methods
compileInstanceDef _ = error "Expected ExprInstanceDef"

compileInstanceMethod :: String -> Type -> Expr -> IrGen ()
compileInstanceMethod className concreteType methodExpr = do
    case methodExpr of
        ExprBindingDef methodName (Forall _ _ methodType) body _ _ -> do
            let mangledName = mangleInstanceMethod className concreteType methodName
            compileFunction mangledName methodType body compileValue
        _ -> error "Expected ExprBindingDef in instance method"

callVTableMethod :: LlvmValue -> Int -> [LlvmValue] -> LlvmType -> IrGen LlvmValue
callVTableMethod vtablePtr methodIndex args retType = do
    funcPtrPtr <-
        saveInstruction
            ( LlvmGetElementPtr
                (getValueType vtablePtr)
                vtablePtr
                [intLiteral 0, intLiteral methodIndex]
                False
            )
            (LlvmPointer LlvmPtr)

    funcPtr <- saveInstruction (LlvmLoad funcPtrPtr) LlvmPtr

    saveInstruction (LlvmCall funcPtr retType args) retType
