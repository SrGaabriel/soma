{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Logging.Trees where

import Alloy.Build hiding (Name)
import Circuit.Ir
import Control.Monad.State
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Format.Trees (TreeShow (..))
import Metal.Expr
import Metal.Function
import Metal.Metadata (FunctionAttributes (..))
import Metal.Module
import Project.Name (nameToString)

indent :: Int -> String -> String
indent n s = replicate n ' ' ++ s

commaSep :: [String] -> String
commaSep = intercalate ", "

instance TreeShow MetallicLiteral where
    treeShow (MInt i) = show i
    treeShow (MBool b) = show b
    treeShow (MString s) = show s

instance TreeShow TypedArm where
    treeShow (MCaseArm pats body) =
        "(" ++ unwords (map show pats) ++ ") => " ++ treeShow body

instance TreeShow TypedExpr where
    treeShow (MVar n _ _) = nameToString n
    treeShow (MLit lit _) = treeShow lit
    treeShow (MCall f args _ _) =
        treeShow f ++ "(" ++ commaSep (map treeShow args) ++ ")"
    treeShow (MTypeApp e tys _ _) =
        treeShow e ++ "[" ++ commaSep (map treeShow tys) ++ "]"
    treeShow (MLet n v b _ _) =
        "let " ++ nameToString n ++ " = " ++ treeShow v ++ " in " ++ treeShow b
    treeShow (MConstruct cname _ fields _ _) =
        nameToString cname ++ " " ++ unwords (map treeShow fields)
    treeShow (MArrayLit es _ _) =
        "[" ++ commaSep (map treeShow es) ++ "]"
    treeShow (MTuple es _ _) =
        "(" ++ commaSep (map treeShow es) ++ ")"
    treeShow (MCase scr arms mdef _ _) =
        "case ("
            ++ commaSep (map treeShow scr)
            ++ ") of { "
            ++ intercalate " | " (map treeShow arms)
            ++ maybe "" (\d -> " | _ => " ++ treeShow d) mdef
            ++ " }"
    treeShow (MFieldAccess e ix _ _) =
        treeShow e ++ "." ++ show ix
    treeShow (MLambda params body _ _) =
        "(\\" ++ commaSep (map (nameToString . fst) params) ++ " -> " ++ treeShow body ++ ")"
    treeShow (MIf cond ifBranch elseBranch _ _) =
        "if " ++ treeShow cond ++ " then " ++ treeShow ifBranch ++ " else " ++ treeShow elseBranch
    treeShow (MPanic msg _ _) = "panic " ++ show msg
    treeShow (MClosure liftedName captured _ _) =
        "closure(" ++ nameToString liftedName ++ ", [" ++ commaSep (map (nameToString . fst) captured) ++ "])"

instance TreeShow MetallicFunction where
    treeShow (MetallicFunction name params ret body _) =
        "def "
            ++ nameToString name
            ++ "("
            ++ commaSep [nameToString n ++ ": " ++ treeShow t | (n, t) <- params]
            ++ ")"
            ++ " -> "
            ++ treeShow ret
            ++ " = "
            ++ treeShow body

instance TreeShow MetallicTypeDef where
    treeShow (MAlgebraicType nm ctors) =
        "data " ++ nameToString nm ++ " = " ++ intercalate " | " (map treeShow ctors)
    treeShow (MStructType nm ctorNm fields) =
        "struct " ++ nameToString nm ++ " = " ++ nameToString ctorNm ++ " " ++ unwords (map treeShow fields)
    treeShow (MRecordType nm fields) =
        "record " ++ nameToString nm ++ " { " ++ commaSep [nameToString n ++ ": " ++ treeShow t | (n, t) <- fields] ++ " }"

instance TreeShow MetallicConstructor where
    treeShow (MetallicConstructor nm _ fields) =
        nameToString nm ++ if null fields then "" else " " ++ unwords (map treeShow fields)

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
    treeShow (MetallicModule name funs tys insts tcs) =
        unlines
            $ ["-- Metal module: " ++ name]
                ++ map (("  " ++) . treeShow) tys
                ++ ["-- Metal (HIR) Functions:"]
                ++ map (("  " ++) . treeShow) funs
                ++ ["-- Metal (HIR) Instances:"]
                ++ map (("  " ++) . treeShow) insts
                ++ ["-- Metal (HIR) TypeClasses:"]
                ++ map (("  " ++) . show) tcs

instance TreeShow AConst where
    treeShow (Alloy.Build.CInt i) = show i
    treeShow (Alloy.Build.CBool b) = show b
    treeShow (CString s) = show s
    treeShow CUnit = "()"

instance TreeShow AOperand where
    treeShow (OpVar n) = nameToString n
    treeShow (OpConst c) = treeShow c

instance TreeShow ACallable where
    treeShow (Direct n) = nameToString n
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
    treeShow (OpSelect cond t f) = "select " ++ treeShow cond ++ " ? " ++ treeShow t ++ " : " ++ treeShow f
    treeShow (OpLoad a) = "load " ++ treeShow a
    treeShow (OpAllocStack t) = "alloca[stack] " ++ treeShow t
    treeShow (OpAllocHeap t) = "alloca[heap] " ++ treeShow t
    treeShow (OpCall callee args) =
        treeShow callee ++ "(" ++ commaSep (map treeShow args) ++ ")"
    treeShow (OpConstruct{acTypeName, acTag, acFields}) =
        "construct " ++ acTypeName ++ "#" ++ show acTag ++ "(" ++ commaSep (map treeShow acFields) ++ ")"
    treeShow (OpTagOf a) = "tag_of " ++ treeShow a
    treeShow (OpArrayLength a) = "array_length " ++ treeShow a
    treeShow (OpCons element arr) = "cons " ++ treeShow element ++ " " ++ treeShow arr
    treeShow (OpArrayTail a) = "array_tail " ++ treeShow a
    treeShow (OpProject a ix) = treeShow a ++ "." ++ show ix
    treeShow (OpIndex a ix) = treeShow a ++ "[" ++ treeShow ix ++ "]"
    treeShow (OpMakeArray xs) = "[" ++ commaSep (map treeShow xs) ++ "]"
    treeShow (OpMakeTuple xs) = "(" ++ commaSep (map treeShow xs) ++ ")"
    treeShow (OpGetDict className ty) = "get_dict " ++ nameToString className ++ " for " ++ treeShow ty
    treeShow (OpDictCall dict methodIdx method args) = "dict_call " ++ treeShow dict ++ "[" ++ show methodIdx ++ "]." ++ nameToString method ++ "(" ++ commaSep (map treeShow args) ++ ")"
    treeShow (OpDup label val) = "dup[" ++ show label ++ "] " ++ treeShow val
    treeShow (OpDupProj0 handle) = "proj0 " ++ treeShow handle
    treeShow (OpDupProj1 handle) = "proj1 " ++ treeShow handle
    treeShow (OpWrapClosure fn) = "wrap_closure " ++ treeShow fn
    treeShow (OpAllocClosure fn arity envSz) = "alloc_closure " ++ treeShow fn ++ " arity=" ++ show arity ++ " env=" ++ show envSz
    treeShow (OpClosureSetEnv closure idx val) = "closure_set_env " ++ treeShow closure ++ "[" ++ show idx ++ "] := " ++ treeShow val
    treeShow (OpClosureGetEnv closure idx) = "closure_get_env " ++ treeShow closure ++ "[" ++ show idx ++ "]"
    treeShow (OpClosureGetFunc closure) = "closure_get_func " ++ treeShow closure
    -- Specialized closure duplication ops
    treeShow (OpDupClosure label closure slotInfo) = "dup_closure[" ++ show label ++ "] " ++ treeShow closure ++ " slots=" ++ show slotInfo
    treeShow (OpDupClosureProj0 handle envSz slotInfo) = "dup_closure_proj0 " ++ treeShow handle ++ " env=" ++ show envSz ++ " slots=" ++ show slotInfo
    treeShow (OpDupClosureProj1 handle envSz slotInfo) = "dup_closure_proj1 " ++ treeShow handle ++ " env=" ++ show envSz ++ " slots=" ++ show slotInfo
    treeShow (OpClosureGetEnvDirect closure idx) = "closure_get_env_direct " ++ treeShow closure ++ "[" ++ show idx ++ "]"
    treeShow (OpClosureGetEnvSUP closure idx) = "closure_get_env_sup " ++ treeShow closure ++ "[" ++ show idx ++ "]"
    -- Parallel projection ops
    treeShow (OpParProj0 handle workEst) = "par_proj0 " ++ treeShow handle ++ " work=" ++ show workEst
    treeShow (OpParProj1 handle workEst) = "par_proj1 " ++ treeShow handle ++ " work=" ++ show workEst
    treeShow (OpParClosureProj0 handle envSz slotInfo workEst) = "par_closure_proj0 " ++ treeShow handle ++ " env=" ++ show envSz ++ " slots=" ++ show slotInfo ++ " work=" ++ show workEst
    treeShow (OpParClosureProj1 handle envSz slotInfo workEst) = "par_closure_proj1 " ++ treeShow handle ++ " env=" ++ show envSz ++ " slots=" ++ show slotInfo ++ " work=" ++ show workEst
    treeShow (OpPanic msg) = "panic \"" ++ msg ++ "\""
    -- Graph reduction ops
    treeShow (OpGraphInit n) = "graph_init workers=" ++ show n
    treeShow OpGraphShutdown = "graph_shutdown"
    treeShow (OpGraphNum v) = "graph_num " ++ treeShow v
    treeShow (OpGraphAdd l r) = "graph_add " ++ treeShow l ++ " " ++ treeShow r
    treeShow (OpGraphSub l r) = "graph_sub " ++ treeShow l ++ " " ++ treeShow r
    treeShow (OpGraphMul l r) = "graph_mul " ++ treeShow l ++ " " ++ treeShow r
    treeShow (OpGraphDiv l r) = "graph_div " ++ treeShow l ++ " " ++ treeShow r
    treeShow (OpGraphMod l r) = "graph_mod " ++ treeShow l ++ " " ++ treeShow r
    treeShow (OpGraphCall fnName args) = "graph_call fn=\"" ++ nameToString fnName ++ "\" args=[" ++ intercalate ", " (map treeShow args) ++ "]"
    treeShow (OpGraphReduce root) = "graph_reduce " ++ treeShow root
    treeShow (OpGraphExtractNum term) = "graph_extract_num " ++ treeShow term
    treeShow (OpGraphRegisterFunc name arity impl) = "graph_register_func \"" ++ nameToString name ++ "\" arity=" ++ show arity ++ " impl=" ++ treeShow impl
    treeShow (OpGraphDup label val) = "graph_dup[" ++ show label ++ "] " ++ treeShow val
    treeShow (OpGraphDupGetProj0 dup) = "graph_dup_proj0 " ++ treeShow dup
    treeShow (OpGraphDupGetProj1 dup) = "graph_dup_proj1 " ++ treeShow dup
    treeShow (OpGraphSup label left right) = "graph_sup[" ++ show label ++ "] " ++ treeShow left ++ " " ++ treeShow right
    treeShow OpGraphEra = "graph_era"
    treeShow (OpGraphCon fst' snd') = "graph_con " ++ treeShow fst' ++ " " ++ treeShow snd'
    treeShow (OpGraphConGet con idx) = "graph_con_get " ++ treeShow con ++ "[" ++ show idx ++ "]"
    treeShow (OpGraphLam param body) = "graph_lam " ++ treeShow param ++ " -> " ++ treeShow body
    treeShow (OpGraphRef fnName idx arg) = "graph_ref[" ++ show idx ++ "] \"" ++ nameToString fnName ++ "\" " ++ treeShow arg
    treeShow (OpGraphApp fn arg) = "graph_app " ++ treeShow fn ++ " @ " ++ treeShow arg
    treeShow (OpGraphClosure funcIdx arity envVals) =
        "graph_closure[" ++ show funcIdx ++ ", arity=" ++ show arity ++ "](" ++ intercalate ", " (map treeShow envVals) ++ ")"
    treeShow (OpGraphClosureApp clo arg) = "graph_closure_app " ++ treeShow clo ++ " @ " ++ treeShow arg
    treeShow (OpGraphClosureGetEnv clo idx) = "graph_closure_get_env " ++ treeShow clo ++ "[" ++ show idx ++ "]"
    treeShow (OpFork term workEst) = "fork " ++ treeShow term ++ " work=" ++ show workEst
    treeShow (OpJoin handle) = "join " ++ treeShow handle

instance TreeShow AEffect where
    treeShow (EffStore dst v) = "store " ++ treeShow dst ++ " := " ++ treeShow v
    treeShow (EffStoreIndex arr ix v) = "store " ++ treeShow arr ++ "[" ++ treeShow ix ++ "] := " ++ treeShow v
    treeShow (EffDrop a) = "drop " ++ treeShow a
    treeShow (EffClosureSetEnv closure idx val) = "closure_set_env " ++ treeShow closure ++ "[" ++ show idx ++ "] := " ++ treeShow val
    treeShow (EffGraphInit n) = "graph_init workers=" ++ show n
    treeShow EffGraphShutdown = "graph_shutdown"
    treeShow (EffGraphRegisterFunc name arity impl) = "graph_register_func \"" ++ nameToString name ++ "\" arity=" ++ show arity ++ " impl=" ++ treeShow impl

instance TreeShow AInstr where
    treeShow (ILet n ty op) = nameToString n ++ " = " ++ treeShow op ++ " (" ++ treeShow ty ++ ")"
    treeShow (IEffect eff) = treeShow eff

instance TreeShow ATerminator where
    treeShow (ABr lbl args) =
        "br " ++ nameToString lbl ++ argsS
      where
        argsS = if null args then "" else " (" ++ commaSep (map treeShow args) ++ ")"
    treeShow (ACondBr c t ta f fa) =
        "br_if "
            ++ treeShow c
            ++ " then "
            ++ nameToString t
            ++ withArgs ta
            ++ " else "
            ++ nameToString f
            ++ withArgs fa
      where
        withArgs xs = if null xs then "" else " (" ++ commaSep (map treeShow xs) ++ ")"
    treeShow (ASwitch scr cases mdef) =
        "switch "
            ++ treeShow scr
            ++ " { "
            ++ intercalate ", " [show i ++ " -> " ++ nameToString lbl | (i, lbl) <- cases]
            ++ maybe "" ((", default -> " ++) . nameToString) mdef
            ++ " }"
    treeShow (ARet Nothing) = "ret"
    treeShow (ARet (Just v)) = "ret " ++ treeShow v
    treeShow AUnreachable = "unreachable"

instance TreeShow ABlock where
    treeShow (ABlock nm params instrs term) =
        nameToString nm
            ++ paramsS
            ++ ":\n"
            ++ unlines (map (indent 2 . treeShow) instrs)
            ++ indent 2 (treeShow term)
      where
        paramsS =
            if null params
                then ""
                else "(" ++ commaSep [nameToString n ++ ": " ++ treeShow t | (n, t) <- params] ++ ")"

instance TreeShow AlloyFunction where
    treeShow (AlloyFunction nm params ret entry blks constraints attrs) =
        (if faInline attrs then "inline " else "")
            ++ "func "
            ++ nameToString nm
            ++ "("
            ++ commaSep [nameToString n ++ ": " ++ treeShow t | (n, t) <- params]
            ++ ")"
            ++ " -> "
            ++ treeShow ret
            ++ (if null constraints then "" else " where " ++ show constraints)
            ++ " {"
            ++ "\n  entry = "
            ++ nameToString entry
            ++ "\n"
            ++ unlines (map (indent 2 . treeShow) blks)
            ++ "}"

instance TreeShow AlloyModule where
    treeShow (AlloyModule nm fns dicts tcs _structTypes _typeDefs) =
        "module "
            ++ nm
            ++ "\n"
            ++ (if null dicts then "" else "-- Dictionaries:\n" ++ unlines (map (indent 2 . show) dicts) ++ "\n")
            ++ (if null tcs then "" else "-- TypeClasses:\n" ++ unlines (map (indent 2 . show) tcs) ++ "\n")
            ++ unlines (map (indent 2 . treeShow) fns)

-- ============================================================================
-- Circuit IR Pretty Printing
-- ============================================================================

-- | Pretty print a complete module
prettyCircuit :: CModule -> String
prettyCircuit m =
    unlines
        $ [ "-- Circuit Module: " ++ cmName m
          , "-- Linearized: " ++ show (cmIsLinearized m)
          , ""
          , "-- Types"
          ]
            ++ map prettyTypeDef (cmTypes m)
            ++ ["", "-- Functions"]
            ++ map prettyFunction (cmFunctions m)

-- | Pretty print a type definition
prettyTypeDef :: CTypeDef -> String
prettyTypeDef td =
    "type "
        ++ nameToString (ctName td)
        ++ " = "
        ++ intercalate " | " (map prettyCtor (ctConstructors td))
  where
    prettyCtor c = nameToString (ccName c) ++ "/" ++ show (ccArity c) ++ "#" ++ show (ccTag c)

-- | Pretty print a function
prettyFunction :: CFunction -> String
prettyFunction f =
    unlines
        [ "@" ++ nameToString (cfName f) ++ " " ++ unwords (map (nameToString . fst) (cfParams f)) ++ " ="
        , "  " ++ prettyTerm (cfBody f)
        ]

-- | Pretty print a term
prettyTerm :: CTerm -> String
prettyTerm = go 0
  where
    go :: Int -> CTerm -> String
    go _ (CVar n _) = nameToString n
    go d (CLam n _ body) =
        "λ" ++ nameToString n ++ ". " ++ go d body
    go d (CApp f x _) =
        "(" ++ go d f ++ " " ++ go d x ++ ")"
    go d (CLet n _ val body) =
        "let " ++ nameToString n ++ " = " ++ go d val ++ " in " ++ go d body
    go d (CSup l a b _) =
        "&" ++ show l ++ "{" ++ go d a ++ ", " ++ go d b ++ "}"
    go d (CDup n _ l val body) =
        "!" ++ nameToString n ++ " &" ++ show l ++ " = " ++ go d val ++ "; " ++ go d body
    go _ (CDp0 n _) = nameToString n ++ "₀"
    go _ (CDp1 n _) = nameToString n ++ "₁"
    go _ CEra = "*"
    go d (CErase val body) = "erase " ++ go d val ++ "; " ++ go d body
    go _ (CRef n _) = "@" ++ nameToString n
    go _ (Circuit.Ir.CInt i) = show i
    go _ (Circuit.Ir.CBool True) = "true"
    go _ (Circuit.Ir.CBool False) = "false"
    go _ (CStr s) = show s
    go d (CTag tag fields _) =
        "<" ++ show tag ++ concatMap (\f -> ", " ++ go d f) fields ++ ">"
    go d (CCase scrut arms mdef _) =
        "case "
            ++ go d scrut
            ++ " of { "
            ++ intercalate "; " (map (prettyArm d) arms)
            ++ maybe "" (\def -> "; _ -> " ++ go d def) mdef
            ++ " }"
      where
        prettyArm dd (tag, fieldsWithTypes, body) =
            "<" ++ show tag ++ concatMap (\(n, _) -> ", " ++ nameToString n) fieldsWithTypes ++ "> -> " ++ go dd body
    go d (CBinOp op a b) =
        "((" ++ prettyBinOp op ++ " " ++ go d a ++ ") " ++ go d b ++ ")"
    go d (CCmpOp op a b) =
        "((" ++ prettyCmpOp op ++ " " ++ go d a ++ ") " ++ go d b ++ ")"
    go d (CUnaryOp op a) =
        prettyUnaryOp op ++ go d a
    go _ (CClosure liftedName capturedVars _) =
        "closure(" ++ nameToString liftedName ++ ", [" ++ intercalate ", " (map (nameToString . fst) capturedVars) ++ "])"
    go d (CClosureGetEnv closure idx _) =
        "closure_get_env(" ++ go d closure ++ ", " ++ show idx ++ ")"
    go d (CProject expr idx _) =
        go d expr ++ "." ++ show idx
    go _ (CPanic msg _) =
        "panic \"" ++ msg ++ "\""
    go d (CFork n _ comp body) =
        "fork " ++ nameToString n ++ " = " ++ go d comp ++ " in " ++ go d body
    go _ (CJoin n _) =
        "join " ++ nameToString n

-- | Pretty print binary operators
prettyBinOp :: BinOp -> String
prettyBinOp = \case
    OpAdd -> "+"
    OpSub -> "-"
    OpMul -> "*"
    OpDiv -> "/"
    OpMod -> "%"
    OpAnd -> "&"
    OpOr -> "|"
    OpXor -> "^"
    OpShl -> "<<"
    OpShr -> ">>"

-- | Pretty print comparison operators
prettyCmpOp :: CmpOp -> String
prettyCmpOp = \case
    OpEq -> "=="
    OpNe -> "!="
    OpLt -> "<"
    OpLe -> "<="
    OpGt -> ">"
    OpGe -> ">="

-- | Pretty print unary operators
prettyUnaryOp :: UnaryOp -> String
prettyUnaryOp = \case
    OpNot -> "!"
    OpNeg -> "-"

-- | Compact single-line representation
prettyTermCompact :: CTerm -> String
prettyTermCompact = prettyTerm

-- | Multi-line indented representation for complex terms
prettyTermIndented :: Int -> CTerm -> String
prettyTermIndented = go
  where
    ind n = replicate (n * 2) ' '

    go :: Int -> CTerm -> String
    go n (CLet name _ val body) =
        ind n
            ++ "let "
            ++ nameToString name
            ++ " =\n"
            ++ go (n + 1) val
            ++ "\n"
            ++ ind n
            ++ "in\n"
            ++ go (n + 1) body
    go n (CLam name _ body) =
        ind n
            ++ "λ"
            ++ nameToString name
            ++ ".\n"
            ++ go (n + 1) body
    go n (CDup name _ l val body) =
        ind n
            ++ "!"
            ++ nameToString name
            ++ " &"
            ++ show l
            ++ " =\n"
            ++ go (n + 1) val
            ++ "\n"
            ++ ind n
            ++ "in\n"
            ++ go (n + 1) body
    go n (CCase scrut arms mdef _) =
        ind n
            ++ "case "
            ++ prettyTerm scrut
            ++ " of\n"
            ++ concatMap (prettyArmIndented (n + 1)) arms
            ++ maybe "" (\d -> ind (n + 1) ++ "_ ->\n" ++ go (n + 2) d ++ "\n") mdef
    go n term = ind n ++ prettyTerm term

    prettyArmIndented n (tag, fieldsWithTypes, body) =
        ind n
            ++ "<"
            ++ show tag
            ++ concatMap (\(name, _) -> ", " ++ nameToString name) fieldsWithTypes
            ++ "> ->\n"
            ++ go (n + 1) body
            ++ "\n"

-- ============================================================================
-- Graph Format
-- ============================================================================

-- | Node types in the interaction net graph
data NodeType
    = NLam Name -- Lambda node with binder name
    | NApp -- Application node
    | NDup Label -- Duplication node with label
    | NSup Label -- Superposition node with label
    | NEra -- Erasure node (value)
    | NErase -- Erase operation (consume value and continue)
    | NVar Name -- Variable reference
    | NDp0 Name -- Dup projection 0
    | NDp1 Name -- Dup projection 1
    | NRef Name -- Function reference
    | NInt Int -- Integer literal
    | NBool Bool -- Boolean literal
    | NStr String -- String literal
    | NLet Name -- Let binding
    | NTag Int -- Tagged value (constructor)
    | NCase Int -- Case with n arms
    | NBinOp BinOp -- Binary operation
    | NCmpOp CmpOp -- Comparison operation
    | NUnaryOp UnaryOp -- Unary operation
    | NClosure Name [Name] -- Closure with lifted name and captured var names
    | NClosureGetEnv Int -- Closure env access with index
    | NProject Int -- Field projection with index
    | NPanic String -- Panic with message
    deriving (Show, Eq)

-- | A node in the graph
data GNode = GNode
    { gnId :: Int
    , gnType :: NodeType
    , gnPorts :: [Port]
    }
    deriving (Show, Eq)

-- | A port connection
data Port
    = PNode Int String -- Connected to node ID at named port
    | PFree String -- Free/unconnected port with name
    deriving (Show, Eq)

-- | State for graph building
data GraphState = GraphState
    { gsNextId :: Int
    , gsNodes :: [GNode]
    , gsVarMap :: Map.Map Name Int -- Variable name -> node ID that binds it
    }

type GraphM = State GraphState

-- | Get a fresh node ID
freshNodeId :: GraphM Int
freshNodeId = do
    s <- get
    put s{gsNextId = gsNextId s + 1}
    pure (gsNextId s)

-- | Add a node to the graph
addNode :: NodeType -> [Port] -> GraphM Int
addNode ntype ports = do
    nid <- freshNodeId
    modify $ \s -> s{gsNodes = GNode nid ntype ports : gsNodes s}
    pure nid

-- | Register a variable binding
bindVar :: Name -> Int -> GraphM ()
bindVar name nid = modify $ \s -> s{gsVarMap = Map.insert name nid (gsVarMap s)}

-- | Look up a variable
lookupVar :: Name -> GraphM (Maybe Int)
lookupVar name = gets (Map.lookup name . gsVarMap)

-- | Pretty print a module in graph format
prettyCircuitGraph :: CModule -> String
prettyCircuitGraph m =
    unlines
        $ [ "-- Circuit Module: " ++ cmName m ++ " (Graph Format)"
          , "-- Linearized: " ++ show (cmIsLinearized m)
          , ""
          ]
            ++ concatMap (\f -> prettyFunctionGraph f ++ [""]) (cmFunctions m)

-- | Pretty print a function in graph format
prettyFunctionGraph :: CFunction -> [String]
prettyFunctionGraph f =
    ["=== Function: " ++ nameToString (cfName f) ++ " ==="]
        ++ ["Parameters: " ++ unwords (map (nameToString . fst) (cfParams f))]
        ++ [""]
        ++ prettyTermGraph (cfBody f)

-- | Pretty print a term as a graph
prettyTermGraph :: CTerm -> [String]
prettyTermGraph term =
    let initState = GraphState 0 [] Map.empty
        (rootId, finalState) = runState (buildGraph term) initState
        nodes = reverse (gsNodes finalState)
    in ["Nodes:"]
        ++ map prettyNode nodes
        ++ ["", "Root: node_" ++ show rootId]

-- | Build the graph from a term, returning the root node ID
buildGraph :: CTerm -> GraphM Int
buildGraph = \case
    CVar n _ -> do
        mNode <- lookupVar n
        case mNode of
            Just nid -> pure nid -- Reference to bound variable
            Nothing -> addNode (NVar n) [PFree "value"]
    CLam n _ body -> do
        bodyId <- do
            lamId <- freshNodeId -- Reserve ID for lambda
            bindVar n lamId -- Bind parameter to lambda node
            buildGraph body
        addNode (NLam n) [PNode bodyId "body", PFree "param"]
    CApp f x _ -> do
        fId <- buildGraph f
        xId <- buildGraph x
        addNode NApp [PNode fId "func", PNode xId "arg", PFree "result"]
    CLet n _ val body -> do
        valId <- buildGraph val
        letId <- freshNodeId
        bindVar n letId
        bodyId <- buildGraph body
        modify $ \s -> s{gsNodes = GNode letId (NLet n) [PNode valId "value", PNode bodyId "body"] : gsNodes s}
        pure letId
    CSup l a b _ -> do
        aId <- buildGraph a
        bId <- buildGraph b
        addNode (NSup l) [PNode aId "left", PNode bId "right", PFree "principal"]
    CDup n _ l val body -> do
        valId <- buildGraph val
        dupId <- freshNodeId
        bindVar n dupId
        bodyId <- buildGraph body
        modify $ \s -> s{gsNodes = GNode dupId (NDup l) [PNode valId "value", PFree "proj0", PFree "proj1", PNode bodyId "body"] : gsNodes s}
        pure dupId
    CDp0 n _ -> addNode (NDp0 n) [PFree "from_dup"]
    CDp1 n _ -> addNode (NDp1 n) [PFree "from_dup"]
    CEra -> addNode NEra []
    CErase val body -> do
        valId <- buildGraph val
        bodyId <- buildGraph body
        addNode NErase [PNode valId "erased", PNode bodyId "body"]
    CRef n _ -> addNode (NRef n) [PFree "value"]
    Circuit.Ir.CInt i -> addNode (NInt i) [PFree "value"]
    Circuit.Ir.CBool b -> addNode (NBool b) [PFree "value"]
    CStr s -> addNode (NStr s) [PFree "value"]
    CTag tag fields _ -> do
        fieldIds <- mapM buildGraph fields
        let fieldPorts = zipWith (\i fid -> PNode fid ("field" ++ show (i :: Integer))) [0 ..] fieldIds
        addNode (NTag tag) (fieldPorts ++ [PFree "value"])
    CCase scrut arms mdef _ -> do
        scrutId <- buildGraph scrut
        armIds <-
            mapM
                ( \(_, fieldsWithTypes, body) -> do
                    caseId <- freshNodeId
                    mapM_ (\(n, _) -> bindVar n caseId) fieldsWithTypes
                    buildGraph body
                )
                arms
        defId <- traverse buildGraph mdef
        let armPorts = zipWith (\i aid -> PNode aid ("arm" ++ show (i :: Integer))) [0 ..] armIds
        let defPort = maybe [] (\d -> [PNode d "default"]) defId
        addNode (NCase (length arms)) ([PNode scrutId "scrutinee"] ++ armPorts ++ defPort)
    CBinOp op a b -> do
        aId <- buildGraph a
        bId <- buildGraph b
        addNode (NBinOp op) [PNode aId "left", PNode bId "right", PFree "result"]
    CCmpOp op a b -> do
        aId <- buildGraph a
        bId <- buildGraph b
        addNode (NCmpOp op) [PNode aId "left", PNode bId "right", PFree "result"]
    CUnaryOp op a -> do
        aId <- buildGraph a
        addNode (NUnaryOp op) [PNode aId "operand", PFree "result"]
    CClosure liftedName capturedVars _ -> do
        -- For closures, we create captured var references
        capturedIds <- mapM (\(n, _) -> lookupVar n >>= maybe (addNode (NVar n) [PFree "value"]) pure) capturedVars
        let capturedPorts = zipWith (\i cid -> PNode cid ("capture" ++ show (i :: Integer))) [0 ..] capturedIds
        addNode (NClosure liftedName (map fst capturedVars)) (capturedPorts ++ [PFree "value"])
    CClosureGetEnv closure idx _ -> do
        closureId <- buildGraph closure
        addNode (NClosureGetEnv idx) [PNode closureId "closure", PFree "value"]
    CProject expr idx _ -> do
        exprId <- buildGraph expr
        addNode (NProject idx) [PNode exprId "expr", PFree "value"]
    CPanic msg _ -> do
        addNode (NPanic msg) [PFree "unreachable"]
    CFork n _ comp body -> do
        compId <- buildGraph comp
        forkId <- freshNodeId
        bindVar n forkId
        bodyId <- buildGraph body
        modify $ \s -> s{gsNodes = GNode forkId (NLet n) [PNode compId "task", PNode bodyId "body"] : gsNodes s}
        pure forkId
    CJoin n _ -> do
        mNode <- lookupVar n
        case mNode of
            Just nid -> pure nid
            Nothing -> addNode (NVar n) [PFree "join"]

-- | Pretty print a single node
prettyNode :: GNode -> String
prettyNode node =
    "  node_"
        ++ show (gnId node)
        ++ ": "
        ++ prettyNodeType (gnType node)
        ++ " { "
        ++ intercalate ", " (map prettyPort (gnPorts node))
        ++ " }"

-- | Pretty print a node type
prettyNodeType :: NodeType -> String
prettyNodeType = \case
    NLam n -> "LAM(" ++ nameToString n ++ ")"
    NApp -> "APP"
    NDup l -> "DUP[" ++ show l ++ "]"
    NSup l -> "SUP[" ++ show l ++ "]"
    NEra -> "ERA"
    NErase -> "ERASE"
    NVar n -> "VAR(" ++ nameToString n ++ ")"
    NDp0 n -> "DP0(" ++ nameToString n ++ ")"
    NDp1 n -> "DP1(" ++ nameToString n ++ ")"
    NRef n -> "REF(@" ++ nameToString n ++ ")"
    NInt i -> "INT(" ++ show i ++ ")"
    NBool b -> "BOOL(" ++ show b ++ ")"
    NStr s -> "STR(" ++ show s ++ ")"
    NLet n -> "LET(" ++ nameToString n ++ ")"
    NTag t -> "TAG[" ++ show t ++ "]"
    NCase n -> "CASE[" ++ show n ++ " arms]"
    NBinOp op -> "BINOP(" ++ prettyBinOp op ++ ")"
    NCmpOp op -> "CMPOP(" ++ prettyCmpOp op ++ ")"
    NUnaryOp op -> "UNOP(" ++ prettyUnaryOp op ++ ")"
    NClosure liftedName captures -> "CLOSURE(" ++ nameToString liftedName ++ ", [" ++ intercalate ", " (map nameToString captures) ++ "])"
    NClosureGetEnv idx -> "CLOSURE_GET_ENV[" ++ show idx ++ "]"
    NProject idx -> "PROJECT[" ++ show idx ++ "]"
    NPanic msg -> "PANIC(\"" ++ msg ++ "\")"

-- | Pretty print a port
prettyPort :: Port -> String
prettyPort (PNode nid name) = name ++ "->node_" ++ show nid
prettyPort (PFree name) = name ++ "->*"
