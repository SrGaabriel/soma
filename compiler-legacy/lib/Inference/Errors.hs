{-# LANGUAGE InstanceSigs #-}

module Inference.Errors (InferenceError (..), getExpression, generateErrorForPurpose) where

import Format.Errors (PrintableError (..))
import Format.Trees (TreeShow (treeShow))
import Inference.Core (UnificationPurpose (..))
import Lexing.Position (Span (..))
import Syntax.Tree (Expr (ExprRoot), exprSpan)
import Typing.Types (Constraint, Kind, Type, constraintClassName, constraintTypes)

data InferenceError
    = FunctionBodyTypeMismatch Expr Type Type
    | FunctionApplicationTypeMismatch Expr Type Type
    | PatternMatchArmTypeMismatch Expr Type Type
    | PatternMatchArmsTypeMismatch Expr Type Type
    | PatternConstructorTypeMismatch Expr Type Type
    | ParamLengthMismatch Expr
    | TupleLengthMismatch Expr [Type] [Type]
    | PatternArityMismatch Expr Int Int
    | BinaryOpTypeMismatch Expr Type Type
    | CircularTypeDependency Expr
    | UnboundVariable Expr String
    | KindedTypeMismatch Expr Type Kind Type Kind
    | KindMismatch Expr Kind Kind
    | MissingSuperclassInstance Expr Type Constraint
    | NotAFunction Expr Type
    | MissingClassConstraint Expr Constraint
    | UnknownTrait Expr String
    | UnknownTypeConstructor Expr String
    | InvalidTypeInstantiation Expr Type
    | IfConditionShouldBeBool Expr Type
    | IfElseBranchTypeMismatch Expr Type Type
    | ReferenceToTypeConstructor Expr String
    | ComposeBlockMustEndWithExpression Expr
    | UnresolvedTypeVariable Expr String Type
    | Debug String
    deriving (Show, Eq)

instance PrintableError InferenceError where
    errorMessage :: InferenceError -> String
    errorMessage (FunctionBodyTypeMismatch _ expected actual) =
        "Function is typed '" ++ treeShow expected ++ "' but its body returns '" ++ treeShow actual ++ "'"
    errorMessage (FunctionApplicationTypeMismatch _ expected actual) =
        "The function call expected the type '" ++ treeShow expected ++ "' but received '" ++ treeShow actual ++ "'"
    errorMessage (PatternMatchArmTypeMismatch _ expected actual) =
        "The pattern match arm should be typed '" ++ treeShow expected ++ "' but is instead '" ++ treeShow actual ++ "'"
    errorMessage (PatternMatchArmsTypeMismatch _ expected actual) =
        "Conflicting pattern match arm types, one is '" ++ treeShow expected ++ "' but this one is '" ++ treeShow actual ++ "'"
    errorMessage (PatternConstructorTypeMismatch _ expected actual) =
        "Pattern constructor produces type '" ++ treeShow actual ++ "' but expected '" ++ treeShow expected ++ "'"
    errorMessage (ParamLengthMismatch _) = "The function has a different number of arguments than provided"
    errorMessage (TupleLengthMismatch _ typ1 typ2) = "The tuples have different lengths: " ++ treeShow typ1 ++ " and " ++ treeShow typ2
    errorMessage (BinaryOpTypeMismatch _ left right) = "Binary operation type mismatch (" ++ treeShow left ++ " and " ++ treeShow right ++ ")"
    errorMessage (CircularTypeDependency _) = "Circular type dependency"
    errorMessage (UnboundVariable _ name) = "Unbound variable '" ++ name ++ "'"
    errorMessage (KindedTypeMismatch _ typ1 knd1 typ2 knd2) =
        "Type mismatch: expected "
            ++ treeShow typ1
            ++ " "
            ++ treeShow knd1
            ++ " but received "
            ++ treeShow typ2
            ++ " "
            ++ treeShow knd2
    errorMessage (NotAFunction _ ty) = "The type " ++ treeShow ty ++ " does not support function application"
    errorMessage (UnknownTypeConstructor _ name) = "Unknown type constructor '" ++ name ++ "'"
    errorMessage (UnknownTrait _ name) = "Unknown trait '" ++ name ++ "'"
    errorMessage (PatternArityMismatch _ expected received) =
        "Pattern arity mismatch, expected " ++ show expected ++ "patterns but received " ++ show received
    errorMessage (KindMismatch _ k1 k2) = "Kind mismatch: expected " ++ treeShow k1 ++ " but received " ++ treeShow k2
    errorMessage (MissingClassConstraint _ constraint) =
        let name = constraintClassName constraint
            typs = constraintTypes constraint
        in case typs of
            [typ] -> "Missing instance: no '" ++ name ++ "' instance for type '" ++ treeShow typ ++ "'"
            _ -> "Missing instance: no '" ++ name ++ "' instance for types (" ++ unwords (map treeShow typs) ++ ")"
    errorMessage (IfConditionShouldBeBool _ actualType) =
        "If condition should be of type 'Bool' but is of type '" ++ treeShow actualType ++ "'"
    errorMessage (InvalidTypeInstantiation _ ty) = "Invalid type instantiation for type '" ++ treeShow ty ++ "'"
    errorMessage (IfElseBranchTypeMismatch _ thenType elseType) =
        "If-Else branches have mismatched types: then branch is '" ++ treeShow thenType ++ "' but else branch is '" ++ treeShow elseType ++ "'"
    errorMessage (ReferenceToTypeConstructor _ name) = "Attempted to reference type constructor '" ++ name ++ "' as a value"
    errorMessage (ComposeBlockMustEndWithExpression _) = "Compose block must end with an expression"
    errorMessage (MissingSuperclassInstance _ typ constraint) =
        let name = constraintClassName constraint
        in "Missing superclass instance: no '" ++ name ++ "' instance for type '" ++ treeShow typ ++ "'"
    errorMessage (UnresolvedTypeVariable _ varName fullType) =
        "Could not infer concrete type for type variable '" ++ varName ++ "' in type '" ++ treeShow fullType ++ "'. Consider adding a type annotation."
    errorMessage (Debug msg) = "Debug: " ++ msg

    errorStart :: InferenceError -> Int
    errorStart (Debug _) = 0
    errorStart err =
        let Span start _ = exprSpan (getExpression err)
        in start

    errorEnd (Debug _) = 0
    errorEnd err =
        let Span _ end = exprSpan (getExpression err)
        in end

    errorDebugDevDetails err = show $ getExpression err

getExpression :: InferenceError -> Expr
getExpression err =
    let expr = getExpression' err
    in case expr of
        ExprRoot _ -> error $ "ROOT ERR: " ++ errorMessage err
        _ -> expr
  where
    getExpression' :: InferenceError -> Expr
    getExpression' (FunctionBodyTypeMismatch expr _ _) = expr
    getExpression' (FunctionApplicationTypeMismatch expr _ _) = expr
    getExpression' (PatternMatchArmTypeMismatch expr _ _) = expr
    getExpression' (PatternMatchArmsTypeMismatch expr _ _) = expr
    getExpression' (PatternConstructorTypeMismatch expr _ _) = expr
    getExpression' (BinaryOpTypeMismatch expr _ _) = expr
    getExpression' (ParamLengthMismatch expr) = expr
    getExpression' (TupleLengthMismatch expr _ _) = expr
    getExpression' (CircularTypeDependency expr) = expr
    getExpression' (UnboundVariable expr _) = expr
    getExpression' (NotAFunction expr _) = expr
    getExpression' (UnknownTypeConstructor expr _) = expr
    getExpression' (PatternArityMismatch expr _ _) = expr
    getExpression' (KindMismatch expr _ _) = expr
    getExpression' (MissingClassConstraint expr _) = expr
    getExpression' (KindedTypeMismatch expr _ _ _ _) = expr
    getExpression' (InvalidTypeInstantiation expr _) = expr
    getExpression' (IfConditionShouldBeBool expr _) = expr
    getExpression' (ReferenceToTypeConstructor expr _) = expr
    getExpression' (UnknownTrait expr _) = expr
    getExpression' (MissingSuperclassInstance expr _ _) = expr
    getExpression' (ComposeBlockMustEndWithExpression expr) = expr
    getExpression' (IfElseBranchTypeMismatch expr _ _) = expr
    getExpression' (UnresolvedTypeVariable expr _ _) = expr
    getExpression' (Debug _) = error "Debug error should not be used in production code"

generateErrorForPurpose :: UnificationPurpose -> Expr -> Type -> Type -> InferenceError
generateErrorForPurpose UnifyFunctionBody expr expected actual =
    FunctionBodyTypeMismatch expr expected actual
generateErrorForPurpose UnifyFunctionApplication expr expected actual =
    FunctionApplicationTypeMismatch expr expected actual
generateErrorForPurpose UnifyPatternMatchArmBody expr expected actual =
    PatternMatchArmTypeMismatch expr expected actual
generateErrorForPurpose UnifyPatternMatchArms expr expected actual =
    PatternMatchArmsTypeMismatch expr expected actual
generateErrorForPurpose UnifyPatternConstructor expr expected actual =
    PatternConstructorTypeMismatch expr expected actual
generateErrorForPurpose UnifyIfCondition expr _ actual =
    IfConditionShouldBeBool expr actual
generateErrorForPurpose UnifyIfElseBranches expr thenType elseType =
    IfElseBranchTypeMismatch expr thenType elseType
