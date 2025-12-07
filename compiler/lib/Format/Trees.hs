{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}

module Format.Trees where

import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Debug.Trace as Debug
import Inference.Core (TypeMap)
import Lexing.Position (Located (..))
import Syntax.Patterns (ParsedPattern, Pattern (..))
import Syntax.Tree (ComposeStmt (..), Expr (..), exprChildren)
import Typing.Currying (uncurryKind)
import Typing.Types (Constraint (..), Kind (..), QualifiedType (Forall), SkolemVar (skName), TyConstructor (..), TyVar (TypeVar, tvId), Type (..))
import qualified Typing.Types as TT

class TreeShow a where
    treeShow :: a -> String

instance TreeShow Kind where
    treeShow KindStar = "*"
    treeShow k@(KindArrow _ _) =
        let (args, ret) = uncurryKind k
        in "(" ++ unwords (map treeShow args) ++ " -> " ++ treeShow ret ++ ")"

instance TreeShow TyVar where
    treeShow (TypeVar name kind) = name ++ " :: " ++ treeShow kind

instance TreeShow Type where
    treeShow (TVar tv) = tvId tv
    treeShow (TSkolem sv) = "«" ++ skName sv ++ "»"
    treeShow (TConstructor (TypeConstructor tyId kind)) =
        let name = TT.tyUniqueName tyId
        in if kind == KindStar
            then name
            else name ++ " " ++ treeShow kind
    treeShow (TApp t1 t2) = "(" ++ treeShow t1 ++ ") <" ++ treeShow t2 ++ ">"
    treeShow (TArrow t1 t2) =
        let left = case t1 of
                TArrow _ _ -> "(" ++ treeShow t1 ++ ")"
                _ -> treeShow t1
        in left ++ " -> " ++ treeShow t2
    treeShow (TUnresolved name) = "?" ++ name

instance TreeShow Constraint where
    treeShow :: Constraint -> String
    treeShow constraint =
        let className = TT.constraintClassName constraint
            types = TT.constraintTypes constraint
        in unwords (map treeShow types) ++ " : " ++ className

instance (TreeShow a) => TreeShow [a] where
    treeShow :: (TreeShow a) => [a] -> String
    treeShow xs = "[" ++ unwords (map treeShow xs) ++ "]"

instance TreeShow Expr where
    treeShow (ExprRoot _) = "Root:"
    treeShow (ExprNum n _) = "Num: " ++ n
    treeShow (ExprStr s _) = "Str: " ++ s
    treeShow (ExprUVar v _) = "UVar: " ++ v
    treeShow (ExprVar sym _) = "Var: " ++ show sym
    treeShow (ExprBool b _) = "Bool: " ++ show b
    treeShow (ExprBlock _ _) = "Block:"
    treeShow (ExprArray _ _) = "Array:"
    treeShow (ExprTuple _ _) = "Tuple:"
    treeShow (ExprApp _ _) = "App:"
    treeShow (ExprLambda args _ _) = "Lambda (" ++ unwords args ++ "):"
    treeShow (ExprImport moduleName imports _) =
        "Import: " ++ moduleName ++ " (" ++ intercalate "," imports ++ ")"
    treeShow (ExprLet name _ _ _) = "Let (" ++ name ++ "):"
    treeShow (ExprPatternMatch{}) = "PatternMatch:"
    treeShow (ExprDerivedPatternMatch _) = "DerivedPatternMatch: "
    treeShow (ExprPatternMatchArm p _ _) =
        "PatternMatchArm: (" ++ unwords (map treeShow p) ++ "):"
    treeShow (ExprBindingDef name (Located _ qType) _ _ _ _) = "BindingDef (" ++ name ++ " : " ++ treeShow qType ++ "):"
    treeShow (ExprIntrinsicDef name (Located _ qType) _) = "IntrinsicDef (" ++ name ++ " : " ++ treeShow qType ++ "):"
    treeShow (ExprDataTypeDef name generics _ _ _ _) = "DataDef (" ++ name ++ ": " ++ treeShow generics ++ "):" -- todo: show constraints
    treeShow (ExprDataConstructor name args _) = "DataConstructor (" ++ name ++ ": " ++ treeShowArgs args ++ "):"
    treeShow (ExprTypeClassDef name (Located _ ty) _ _) = "TypeClassDef (" ++ name ++ ": " ++ treeShow ty ++ "):"
    treeShow (ExprTypeClassBinding name (Located _ qType) _ _) = "TypeClassBinding (" ++ name ++ ": " ++ treeShow qType ++ "):"
    treeShow (ExprInstanceDef constraintType _ _) = "InstanceDef (" ++ treeShow constraintType ++ "):"
    treeShow (ExprIntrinsicInstanceDef (Located _ ty) _) =
        "IntrinsicInstanceDef (" ++ treeShow ty ++ ")"
    treeShow (ExprIntrinsicDataTypeDef name kind _) =
        "IntrinsicDataTypeDef (" ++ name ++ ": " ++ treeShow kind ++ "):"
    treeShow (ExprCompose stms _) =
        "MonadComposition (" ++ intercalate " -> " (map treeShow stms) ++ ")"
    treeShow (ExprIf cond ifBlock elseBlock _) =
        "If ("
            ++ treeShow cond
            ++ "):"
            ++ "\n  Then: "
            ++ treeShow ifBlock
            ++ "\n  Else: "
            ++ treeShow elseBlock

instance TreeShow ComposeStmt where
    treeShow (CSBind name _ _) = "Bind(" ++ name ++ ")"
    treeShow (CSLet name _ _) = "Let(" ++ name ++ ")"
    treeShow (CSExpr _ _) = "Op"

instance TreeShow ParsedPattern where
    treeShow (PVar name _) = "Var (" ++ name ++ ")"
    treeShow (PLit lit _) = "Lit (" ++ show lit ++ ")"
    treeShow (PConstructor name args _) =
        "Constructor (" ++ name ++ ": " ++ treeShow args ++ ")"
    treeShow (PTuple p _) = "Tuple (" ++ unwords (map treeShow p) ++ ")"
    treeShow (PArray p _) = "Array (" ++ unwords (map treeShow p) ++ ")"
    treeShow PWildcard{} = "Wildcard"
    treeShow (PAs name p _) = "As (" ++ name ++ ": " ++ treeShow p ++ ")"

instance (TreeShow a) => TreeShow (Map String a) where
    treeShow :: (TreeShow a) => Map String a -> String
    treeShow m = "{" ++ unwords (map (\(k, v) -> k ++ ": " ++ treeShow v) (Map.toList m)) ++ "}"

treeShowArgs :: [(String, Located Type)] -> String
treeShowArgs args =
    "(" ++ unwords (map (\(name, Located _ t) -> name ++ ": " ++ treeShow t) args) ++ ")"

instance TreeShow QualifiedType where
    treeShow (Forall vars constraints t) =
        if null vars
            then treeShow t
            else
                let varsStr = unwords (map tvId vars)
                    constraintsStr = if null constraints then "" else " where (" ++ intercalate " | " (map treeShow constraints) ++ ")"
                in "∀(" ++ varsStr ++ ")" ++ constraintsStr ++ ". " ++ treeShow t

instance TreeShow TypeMap where
    treeShow :: TypeMap -> String
    treeShow tm =
        "TypeMap:\n"
            ++ unlines (map (\(k, v) -> "  " ++ treeShow k ++ " :: " ++ treeShow v) (Map.toList tm))

instance TreeShow (Map.Map Expr Type) where
    treeShow :: Map.Map Expr Type -> String
    treeShow m =
        "Expr Type Map:\n"
            ++ unlines (map (\(k, v) -> "  " ++ treeShow k ++ " : " ++ treeShow v) (Map.toList m))

treeShowTypeMapL :: Expr -> TypeMap -> String
treeShowTypeMapL expr typeMap = go expr 0
  where
    go e indent' =
        let typeStr = case Map.lookup e typeMap of
                Just t -> " : \ESC[33m" ++ treeShow t ++ "\ESC[0m"
                Nothing -> ""
            indentStr = replicate indent' ' '
            children = exprChildren e
            childLines = concatMap (\c -> go c (indent' + 2)) children
        in indentStr ++ treeShow e ++ typeStr ++ "\n" ++ childLines

prettyDebugAst :: (Monad m) => Expr -> m ()
prettyDebugAst root = prettyDebugAst' root 0
  where
    prettyDebugAst' expr indent' = do
        Debug.traceM $ replicate indent' ' ' ++ treeShow expr
        mapM_ (\child -> prettyDebugAst' child (indent' + 2)) (exprChildren expr)

prettyPrintAst :: Expr -> IO ()
prettyPrintAst root = prettyPrintAst' root 0
  where
    prettyPrintAst' expr indent' = do
        putStrLn $ replicate indent' ' ' ++ treeShow expr
        mapM_ (\child -> prettyPrintAst' child (indent' + 2)) (exprChildren expr)
