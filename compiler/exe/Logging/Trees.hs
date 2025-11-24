{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Logging.Trees where

import Alloy.Build
import Data.List (intercalate)
import Format.Trees (TreeShow (..))
import Metal.Expr
import Metal.Function
import Metal.Module

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
    treeShow (MetallicModule funs tys insts tcs) =
        unlines
            $ ["-- Metal (HIR) Types:"]
                ++ map (("  " ++) . treeShow) tys
                ++ ["-- Metal (HIR) Functions:"]
                ++ map (("  " ++) . treeShow) funs
                ++ ["-- Metal (HIR) Instances:"]
                ++ map (("  " ++) . treeShow) insts
                ++ ["-- Metal (HIR) TypeClasses:"]
                ++ map (("  " ++) . show) tcs

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
    treeShow (OpGetDict className ty) = "get_dict " ++ className ++ " for " ++ treeShow ty
    treeShow (OpDictCall dict methodIdx method args) = "dict_call " ++ treeShow dict ++ "[" ++ show methodIdx ++ "]." ++ method ++ "(" ++ commaSep (map treeShow args) ++ ")"

instance TreeShow AEffect where
    treeShow (EffStore dst v) = "store " ++ treeShow dst ++ " := " ++ treeShow v
    treeShow (EffStoreIndex arr ix v) = "store " ++ treeShow arr ++ "[" ++ treeShow ix ++ "] := " ++ treeShow v
    treeShow (EffDrop a) = "drop " ++ treeShow a

instance TreeShow AInstr where
    treeShow (ILet n ty op) = n ++ " = " ++ treeShow op ++ " (" ++ treeShow ty ++ ")"
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
    treeShow (AlloyFunction nm params ret entry blks constraints) =
        "func "
            ++ nm
            ++ "("
            ++ commaSep [n ++ ": " ++ treeShow t | (n, t) <- params]
            ++ ")"
            ++ " -> "
            ++ treeShow ret
            ++ (if null constraints then "" else " where " ++ show constraints)
            ++ " {"
            ++ "\n  entry = "
            ++ entry
            ++ "\n"
            ++ unlines (map (indent 2 . treeShow) blks)
            ++ "}"

instance TreeShow AlloyModule where
    treeShow (AlloyModule nm fns dicts tcs) =
        "module "
            ++ nm
            ++ "\n"
            ++ (if null dicts then "" else "-- Dictionaries:\n" ++ unlines (map (indent 2 . show) dicts) ++ "\n")
            ++ (if null tcs then "" else "-- TypeClasses:\n" ++ unlines (map (indent 2 . show) tcs) ++ "\n")
            ++ unlines (map (indent 2 . treeShow) fns)
