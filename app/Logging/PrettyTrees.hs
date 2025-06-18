{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Logging.PrettyTrees where

import Syntax.Patterns (Pattern (..))
import Syntax.Tree (Expr (..))
import Typing.Currying (uncurryKind)
import Typing.Types (Constraint (..), Kind (..), QualifiedType (Forall), TyConstructor (..), TyVar (TypeVar, tvName), Type (..))

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
    treeShow (ExprLet name _ _ _) = "Let (" ++ name ++ "):"
    treeShow (ExprPatternMatch _ _ _) = "PatternMatch:"
    treeShow (ExprDerivedPatternMatch _) = "DerivedPatternMatch:"
    treeShow (ExprBindingDef name qType _ _) = "FunctionDef (" ++ name ++ " : " ++ treeShow qType ++ "):"
    treeShow (ExprDataTypeDef name generics _ _) = "DataDef (" ++ name ++ ": " ++ treeShow generics ++ "):"
    treeShow (ExprStructConstructor name args _) = "StructConstructor (" ++ name ++ ": " ++ treeShowArgs args ++ "):"
    treeShow (ExprTypeClassDef name generics _ _) = "TypeClassDef (" ++ name ++ ": " ++ treeShow generics ++ "):"
    treeShow (ExprTypeClassMethod name args returnType _ _) = "TypeClassMethod (" ++ name ++ ": " ++ treeShowArgs args ++ " -> " ++ treeShow returnType ++ "):"
    treeShow (ExprInstanceDef className _ _ _) = "InstanceDef (" ++ className ++ "):"

instance TreeShow Pattern where
    treeShow (PVar name) = "Var (" ++ name ++ ")"
    treeShow (PLit lit) = "Lit (" ++ show lit ++ ")"
    treeShow (PConstructor name args) =
        "Constructor (" ++ name ++ ": " ++ treeShow args ++ ")"
    treeShow (PTuple patterns) = "Tuple (" ++ unwords (map treeShow patterns) ++ ")"
    treeShow (PArray patterns) = "Array (" ++ unwords (map treeShow patterns) ++ ")"
    treeShow (PWildcard) = "Wildcard"
    treeShow (PAs name pattern) = "As (" ++ name ++ ": " ++ treeShow pattern ++ ")"

treeShowArgs :: [(String, Type)] -> String
treeShowArgs args =
    "(" ++ unwords (map (\(name, t) -> name ++ ": " ++ treeShow t) args) ++ ")"

instance TreeShow QualifiedType where
    treeShow (Forall vars constraints t) =
        let varsStr = unwords (map tvName vars)
            constraintsStr = if null constraints then "" else " | " ++ unwords (map treeShow constraints)
        in "forall " ++ varsStr ++ constraintsStr ++ ". " ++ treeShow t
