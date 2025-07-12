{-# LANGUAGE InstanceSigs #-}

module Inference.Errors (InferenceError (..), getExpression, generateErrorForPurpose) where

import Inference.Core (UnificationPurpose (..))
import Lexing.Position (Span (..))
import Logging.Errors (PrintableError (..))
import Logging.PrettyTrees (TreeShow (treeShow))
import Syntax.Tree (Expr (ExprRoot), exprSpan)
import Typing.Types (Constraint (Constraint), Kind, Type)

data InferenceError
    = FunctionBodyTypeMismatch Expr Type Type
    | FunctionApplicationTypeMismatch Expr Type Type
    | PatternMatchArmTypeMismatch Expr Type Type
    | PatternMatchArmsTypeMismatch Expr Type Type
    | ParamLengthMismatch Expr
    | TupleLengthMismatch Expr [Type] [Type]
    | PatternArityMismatch Expr Int Int
    | BinaryOpTypeMismatch Expr Type Type
    | CircularTypeDependency Expr
    | UnboundVariable Expr String
    | KindedTypeMismatch Expr Type Kind Type Kind
    | KindMismatch Expr Kind Kind
    | NotAFunction Expr Type
    | MissingClassConstraint Expr Constraint
    | UnknownTypeConstructor Expr String
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
    errorMessage (PatternArityMismatch _ expected received) =
        "Pattern arity mismatch, expected " ++ show expected ++ "patterns but received " ++ show received
    errorMessage (KindMismatch _ k1 k2) = "Kind mismatch: expected " ++ treeShow k1 ++ " but received " ++ treeShow k2
    errorMessage (MissingClassConstraint _ (Constraint name [typ])) =
        "Missing instance: no '" ++ name ++ "' instance for type '" ++ treeShow typ ++ "'"
    errorMessage (MissingClassConstraint _ (Constraint name typs)) =
        "Missing instance: no '" ++ name ++ "' instance for types (" ++ unwords (map treeShow typs) ++ ")"
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

getExpression' :: InferenceError -> Expr
getExpression' (FunctionBodyTypeMismatch expr _ _) = expr
getExpression' (FunctionApplicationTypeMismatch expr _ _) = expr
getExpression' (PatternMatchArmTypeMismatch expr _ _) = expr
getExpression' (PatternMatchArmsTypeMismatch expr _ _) = expr
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
