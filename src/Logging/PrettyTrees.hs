{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}

module Logging.PrettyTrees where

import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Debug.Trace as Debug
import Inference.Core (TypeMap)
import Syntax.Patterns (Pattern (..))
import Syntax.Tree (ComposeStmt (..), Expr (..), exprChildren)
import Typing.Currying (uncurryKind)
import Typing.Types (Constraint (..), Kind (..), QualifiedType (Forall), SkolemVar (skName), TyConstructor (..), TyVar (TypeVar, tvId), Type (..))
import qualified Typing.Types as TT

import Alloy.Ir
import Metal.Expr
import Metal.Function
import Metal.Module

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
    treeShow (TConstructor (TypeConstructor name kind)) =
        if kind == KindStar
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
    treeShow (ExprBindingDef name qType _ _ _) = "BindingDef (" ++ name ++ " : " ++ treeShow qType ++ "):"
    treeShow (ExprIntrinsicDef name qType _) = "IntrinsicDef (" ++ name ++ " : " ++ treeShow qType ++ "):"
    treeShow (ExprDataTypeDef name generics _ _ _) = "DataDef (" ++ name ++ ": " ++ treeShow generics ++ "):" -- todo: show constraints
    treeShow (ExprDataConstructor name args _) = "DataConstructor (" ++ name ++ ": " ++ treeShowArgs args ++ "):"
    treeShow (ExprTypeClassDef name generics _ _) = "TypeClassDef (" ++ name ++ ": " ++ treeShow generics ++ "):"
    treeShow (ExprTypeClassBinding name qType _ _) = "TypeClassBinding (" ++ name ++ ": " ++ treeShow qType ++ "):"
    treeShow (ExprInstanceDef constraintType _ _) = "InstanceDef (" ++ treeShow constraintType ++ "):"
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

instance TreeShow Pattern where
    treeShow (PVar name) = "Var (" ++ name ++ ")"
    treeShow (PLit lit) = "Lit (" ++ show lit ++ ")"
    treeShow (PConstructor name args) =
        "Constructor (" ++ name ++ ": " ++ treeShow args ++ ")"
    treeShow (PTuple p) = "Tuple (" ++ unwords (map treeShow p) ++ ")"
    treeShow (PArray p) = "Array (" ++ unwords (map treeShow p) ++ ")"
    treeShow PWildcard = "Wildcard"
    treeShow (PAs name p) = "As (" ++ name ++ ": " ++ treeShow p ++ ")"

instance (TreeShow a) => TreeShow (Map String a) where
    treeShow :: (TreeShow a) => Map String a -> String
    treeShow m = "{" ++ unwords (map (\(k, v) -> k ++ ": " ++ treeShow v) (Map.toList m)) ++ "}"

treeShowArgs :: [(String, Type)] -> String
treeShowArgs args =
    "(" ++ unwords (map (\(name, t) -> name ++ ": " ++ treeShow t) args) ++ ")"

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

indent :: Int -> String -> String
indent n s = replicate n ' ' ++ s

commaSep :: [String] -> String
commaSep = intercalate ", "

instance TreeShow MetallicLiteral where
    treeShow (MInt i) = show i
    treeShow (MBool b) = show b
    treeShow (MString s) = show s

instance TreeShow MCaseArm where
    treeShow (MCaseArm pats body) =
        "(" ++ unwords (map treeShow pats) ++ ") => " ++ treeShow body

instance TreeShow MetallicExpr where
    treeShow (MVar n _) = n
    treeShow (MLit lit) = treeShow lit
    treeShow (MCall f args _) =
        treeShow f ++ "(" ++ commaSep (map treeShow args) ++ ")"
    treeShow (MTypeApp e tys _) =
        treeShow e ++ "[" ++ commaSep (map treeShow tys) ++ "]"
    treeShow (MLet n v b _) =
        "let " ++ n ++ " = " ++ treeShow v ++ " in " ++ treeShow b
    treeShow (MConstruct cname _ fields _) =
        cname ++ " " ++ unwords (map treeShow fields)
    treeShow (MArrayLit es _) =
        "[" ++ commaSep (map treeShow es) ++ "]"
    treeShow (MTuple es _) =
        "(" ++ commaSep (map treeShow es) ++ ")"
    treeShow (MCase scr arms mdef _) =
        "case ("
            ++ commaSep (map treeShow scr)
            ++ ") of { "
            ++ intercalate " | " (map treeShow arms)
            ++ maybe "" (\d -> " | _ => " ++ treeShow d) mdef
            ++ " }"
    treeShow (MFieldAccess e ix _) =
        treeShow e ++ "." ++ show ix
    treeShow (MLambda params body _) =
        "(\\" ++ commaSep params ++ " -> " ++ treeShow body ++ ")"
    treeShow (MCompose stms _) =
        "compose: " ++ intercalate "\n|>" (map treeShow stms)
    treeShow (MIf cond ifBranch elseBranch _) =
        "if " ++ treeShow cond ++ " then " ++ treeShow ifBranch ++ " else " ++ treeShow elseBranch
    treeShow (MPanic msg _) = "panic " ++ show msg

instance TreeShow MetallicComposeStmt where
    treeShow (MCBind name expr) = "bind " ++ name ++ " <- " ++ treeShow expr
    treeShow (MCLet name expr) = "let " ++ name ++ " = " ++ treeShow expr
    treeShow (MCExpr expr) = "chain " ++ treeShow expr

instance TreeShow MetallicFunction where
    treeShow (MetallicFunction name params ret body _) =
        "def "
            ++ name
            ++ "("
            ++ commaSep [n ++ ": " ++ treeShow t | (n, t) <- params]
            ++ ")"
            ++ " -> "
            ++ treeShow ret
            ++ " = "
            ++ treeShow body

instance TreeShow MetallicTypeDef where
    treeShow (MAlgebraicType nm ctors) =
        "data " ++ nm ++ " = " ++ intercalate " | " (map treeShow ctors)
    treeShow (MRecordType nm fields) =
        "record " ++ nm ++ " { " ++ commaSep [n ++ ": " ++ treeShow t | (n, t) <- fields] ++ " }"

instance TreeShow MetallicConstructor where
    treeShow (MetallicConstructor nm _ fields) =
        nm ++ if null fields then "" else " " ++ unwords (map treeShow fields)

instance TreeShow MetallicInstance where
    treeShow (MetallicInstance cls ty methods) =
        "instance "
            ++ cls
            ++ " "
            ++ treeShow ty
            ++ " where { "
            ++ intercalate "; " (map treeShow methods)
            ++ " }"

instance TreeShow MetallicModule where
    treeShow (MetallicModule funs tys insts) =
        unlines
            $ ["-- Metal (HIR) Types:"]
                ++ map (("  " ++) . treeShow) tys
                ++ ["-- Metal (HIR) Functions:"]
                ++ map (("  " ++) . treeShow) funs
                ++ ["-- Metal (HIR) Instances:"]
                ++ map (("  " ++) . treeShow) insts

instance TreeShow AConst where
    treeShow (CInt i) = show i
    treeShow (CBool b) = show b
    treeShow (CString s) = show s
    treeShow CUnit = "()"

instance TreeShow AOperand where
    treeShow (OpVar n) = n
    treeShow (OpConst c) = treeShow c

instance TreeShow ACallable where
    treeShow (Direct n) = n
    treeShow (Indirect op) = "*" ++ treeShow op

instance TreeShow ABinOpKind where
    treeShow = show

instance TreeShow AUnaryOpKind where
    treeShow = show

instance TreeShow ACmpOp where
    treeShow = show

instance TreeShow AOp where
    treeShow (OpBin k a b) = "(" ++ treeShow a ++ " " ++ treeShow k ++ " " ++ treeShow b ++ ")"
    treeShow (OpUnary k a) = "(" ++ treeShow k ++ " " ++ treeShow a ++ ")"
    treeShow (OpCmp k a b) = "(" ++ treeShow a ++ " " ++ treeShow k ++ " " ++ treeShow b ++ ")"
    treeShow (OpLoad a) = "load " ++ treeShow a
    treeShow (OpAllocStack t) = "alloca[stack] " ++ treeShow t
    treeShow (OpAllocHeap t) = "alloca[heap] " ++ treeShow t
    treeShow (OpCall callee args) =
        treeShow callee ++ "(" ++ commaSep (map treeShow args) ++ ")"
    treeShow (OpConstruct{acTypeName, acTag, acFields}) =
        "construct " ++ acTypeName ++ "#" ++ show acTag ++ "(" ++ commaSep (map treeShow acFields) ++ ")"
    treeShow (OpTagOf a) = "tag_of " ++ treeShow a
    treeShow (OpProject a ix) = treeShow a ++ "." ++ show ix
    treeShow (OpIndex a ix) = treeShow a ++ "[" ++ treeShow ix ++ "]"
    treeShow (OpMakeArray xs) = "[" ++ commaSep (map treeShow xs) ++ "]"
    treeShow (OpMakeTuple xs) = "(" ++ commaSep (map treeShow xs) ++ ")"

instance TreeShow AEffect where
    treeShow (EffStore dst v) = "store " ++ treeShow dst ++ " := " ++ treeShow v
    treeShow (EffStoreIndex arr ix v) = "store " ++ treeShow arr ++ "[" ++ treeShow ix ++ "] := " ++ treeShow v
    treeShow (EffDrop a) = "drop " ++ treeShow a

instance TreeShow AInstr where
    treeShow (ILet n _ op) = n ++ " = " ++ treeShow op
    treeShow (IEffect eff) = treeShow eff

instance TreeShow ATerminator where
    treeShow (ABr lbl args) =
        "br " ++ lbl ++ argsS
      where
        argsS = if null args then "" else " (" ++ commaSep (map treeShow args) ++ ")"
    treeShow (ACondBr c t ta f fa) =
        "br_if "
            ++ treeShow c
            ++ " then "
            ++ t
            ++ withArgs ta
            ++ " else "
            ++ f
            ++ withArgs fa
      where
        withArgs xs = if null xs then "" else " (" ++ commaSep (map treeShow xs) ++ ")"
    treeShow (ASwitch scr cases mdef) =
        "switch "
            ++ treeShow scr
            ++ " { "
            ++ intercalate ", " [show i ++ " -> " ++ lbl | (i, lbl) <- cases]
            ++ maybe "" (", default -> " ++) mdef
            ++ " }"
    treeShow (ARet Nothing) = "ret"
    treeShow (ARet (Just v)) = "ret " ++ treeShow v
    treeShow AUnreachable = "unreachable"

instance TreeShow ABlock where
    treeShow (ABlock nm params instrs term) =
        nm
            ++ paramsS
            ++ ":\n"
            ++ unlines (map (indent 2 . treeShow) instrs)
            ++ indent 2 (treeShow term)
      where
        paramsS =
            if null params
                then ""
                else "(" ++ commaSep [n ++ ": " ++ treeShow t | (n, t) <- params] ++ ")"

instance TreeShow AlloyFunction where
    treeShow (AlloyFunction nm params ret entry blks) =
        "func "
            ++ nm
            ++ "("
            ++ commaSep [n ++ ": " ++ treeShow t | (n, t) <- params]
            ++ ")"
            ++ " -> "
            ++ treeShow ret
            ++ " {"
            ++ "\n  entry = "
            ++ entry
            ++ "\n"
            ++ unlines (map (indent 2 . treeShow) blks)
            ++ "}"

instance TreeShow AlloyModule where
    treeShow (AlloyModule nm fns) =
        "module "
            ++ nm
            ++ "\n"
            ++ unlines (map (indent 2 . treeShow) fns)
