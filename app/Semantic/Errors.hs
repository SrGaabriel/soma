{-# LANGUAGE InstanceSigs #-}

module Semantic.Errors where

import Lexing.Position (Span (..))
import Logging.ErrorPrinter (PrintableError (..))
import Logging.PrettyTrees (TreeShow (treeShow))
import Syntax.Tree (Expr, exprSpan)
import Typing.Types (Kind, Type)

data SemanticError
    = TypeMismatch Expr Type Type
    | ParamLengthMismatch Expr
    | TupleLengthMismatch Expr [Type] [Type]
    | ArityMismatch Expr
    | BinaryOpTypeMismatch Expr Type Type
    | CircularTypeDependency Expr
    | UnboundVariable Expr String
    | KindMismatch Expr Kind Kind
    | UntypedExpression Expr
    | NotAFunction Expr Type
    | UnsatisfiedConstraints Expr [String]
    | UnknownTypeConstructor Expr String Kind
    deriving (Show, Eq)

instance PrintableError SemanticError where
    errorMessage :: SemanticError -> String
    errorMessage (TypeMismatch _ t1 t2) = "Cannot conciliate types '" ++ show t1 ++ "' and '" ++ show t2 ++ "'"
    errorMessage (ParamLengthMismatch _) = "The function has a different number of arguments than provided"
    errorMessage (TupleLengthMismatch _ typ1 typ2) = "The tuples have different lengths: " ++ show typ1 ++ " and " ++ show typ2
    errorMessage (BinaryOpTypeMismatch _ left right) = "Binary operation type mismatch (" ++ show left ++ " and " ++ show right ++ ")"
    errorMessage (CircularTypeDependency _) = "Circular type dependency"
    errorMessage (UnboundVariable _ name) = "Unbound variable '" ++ name ++ "'"
    errorMessage (UntypedExpression expr) = "The expression " ++ show expr ++ " is untyped"
    errorMessage (NotAFunction _ ty) = "The type " ++ show ty ++ " does not support function application"
    errorMessage (UnknownTypeConstructor _ name kind) = "Unknown constructor '" ++ name ++ "' kinded " ++ treeShow kind
    errorMessage (ArityMismatch expr) = "The expression " ++ show expr ++ " has an incorrect arity"
    errorMessage (KindMismatch _ k1 k2) = "Kind mismatch: expected " ++ treeShow k1 ++ " but received " ++ treeShow k2
    errorMessage (UnsatisfiedConstraints expr constraints) =
        "The expression " ++ show expr ++ " has unsatisfied constraints: " ++ unwords constraints

    errorStart :: SemanticError -> Int
    errorStart err =
        let Span start _ = exprSpan (getExpression err)
        in start

    errorEnd err =
        let Span _ end = exprSpan (getExpression err)
        in end

getExpression :: SemanticError -> Expr
getExpression (TypeMismatch expr _ _) = expr
getExpression (BinaryOpTypeMismatch expr _ _) = expr
getExpression (ParamLengthMismatch expr) = expr
getExpression (TupleLengthMismatch expr _ _) = expr
getExpression (CircularTypeDependency expr) = expr
getExpression (UnboundVariable expr _) = expr
getExpression (UntypedExpression expr) = expr
getExpression (NotAFunction expr _) = expr
getExpression (UnknownTypeConstructor expr _ _) = expr
getExpression (ArityMismatch expr) = expr
getExpression (KindMismatch expr _ _) = expr
getExpression (UnsatisfiedConstraints expr _) = expr
