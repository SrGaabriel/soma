{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Logging.PrettyTrees where

import Syntax.Tree (Expr (..))
import Typing.Currying (uncurryKind)
import Typing.Types (Constraint (..), Kind (..), TyConstructor (..), TyVar (TypeVar, tvName), Type (..))

class TreeShow a where
    treeShow :: a -> String

instance TreeShow Kind where
    treeShow (KindStar) = "*"
    treeShow k@(KindArrow _ _) =
        let (args, ret) = uncurryKind k
        in "(" ++ unwords (map treeShow args) ++ " -> " ++ treeShow ret ++ ")"

instance TreeShow TyVar where
    treeShow (TypeVar name kind) = name ++ " :: " ++ treeShow kind

instance TreeShow Type where
    treeShow (TVar tv) = "<" ++ tvName tv ++ ">"
    treeShow (TConstructor (TypeConstructor name kind)) =
        if kind == KindStar
            then name
            else name ++ " " ++ treeShow kind
    treeShow (TApp t1 t2) = "(" ++ treeShow t1 ++ " " ++ treeShow t2 ++ ")"
    treeShow (TArrow t1 t2) = "(" ++ treeShow t1 ++ " -> " ++ treeShow t2 ++ ")"
    treeShow (TForall tv t) = "∀ " ++ tvName tv ++ ". " ++ treeShow t
    treeShow (TUnresolved name kind) =
        if kind == KindStar
            then "'" ++ name ++ "'"
            else "'" ++ name ++ "' :: " ++ treeShow kind
    treeShow (TTuple ts) = "(" ++ unwords (map treeShow ts) ++ ")"
    treeShow (TConstrained t1 t2) = treeShow t1 ++ " : " ++ treeShow t2

instance TreeShow Constraint where
    treeShow :: Constraint -> String
    treeShow (Constraint className varnames) = unwords (map treeShow varnames) ++ " : " ++ className

instance (TreeShow a) => TreeShow [a] where
    treeShow :: (TreeShow a) => [a] -> String
    treeShow xs = "[" ++ unwords (map treeShow xs) ++ "]"

instance TreeShow Expr where
    treeShow (ExprRoot _) = "Root:"
    treeShow (ExprNum n _) = "Num: " ++ n
    treeShow (ExprStr s _) = "Str: " ++ s
    treeShow (ExprVar v _) = "Var: " ++ v
    treeShow (ExprBool b _) = "Bool: " ++ show b
    treeShow (ExprBlock _ _) = "Block:"
    treeShow (ExprArray _ _) = "Array:"
    treeShow (ExprTuple _ _) = "Tuple:"
    treeShow (ExprApp _ _) = "App:"
    treeShow (ExprLambda args _ _) = "Lambda (" ++ unwords args ++ "):"
    treeShow (ExprBinaryOp op _ _) = "BinaryOp (" ++ show op ++ "):"
    treeShow (ExprLet name _ _ _) = "Let (" ++ name ++ "):"
    treeShow (ExprFunctionDef name args returns _ _) = "FunctionDef (" ++ name ++ ": " ++ treeShowArgs args ++ " -> " ++ treeShow returns ++ "):"
    treeShow (ExprConstantDef name cType _ _) = "ConstantDef (" ++ name ++ ": " ++ treeShow cType ++ "):"
    treeShow (ExprStructDef name generics _ _) = "StructDef (" ++ name ++ ": " ++ treeShow generics ++ "):"
    treeShow (ExprStructConstructor name args _) = "StructConstructor (" ++ name ++ ": " ++ treeShowArgs args ++ "):"
    treeShow (ExprTypeClassDef name generics _ _) = "TypeClassDef (" ++ name ++ ": " ++ treeShow generics ++ "):"
    treeShow (ExprTypeClassMethod name args returnType _ _) = "TypeClassMethod (" ++ name ++ ": " ++ treeShowArgs args ++ " -> " ++ treeShow returnType ++ "):"

treeShowArgs :: [(String, Type)] -> String
treeShowArgs args =
    "(" ++ unwords (map (\(name, t) -> name ++ ": " ++ treeShow t) args) ++ ")"
