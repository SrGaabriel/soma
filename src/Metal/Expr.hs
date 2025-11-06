module Metal.Expr where

import Syntax.Patterns (Pattern)
import Typing.Types (Type, boolType, intType, strType)

data MetallicExpr
    = MVar String Type
    | MLit MetallicLiteral
    | MCall MetallicExpr [MetallicExpr] Type
    | MTypeApp MetallicExpr [Type] Type
    | MLet String MetallicExpr MetallicExpr Type
    | MLambda [String] MetallicExpr Type
    | MConstruct String Int [MetallicExpr] Type
    | MArrayLit [MetallicExpr] Type
    | MTuple [MetallicExpr] Type
    | MIf MetallicExpr MetallicExpr MetallicExpr Type
    | MCase [MetallicExpr] [MCaseArm] (Maybe MetallicExpr) Type
    | MFieldAccess MetallicExpr Int Type
    | MPanic String Type
    | MCompose [MetallicComposeStmt] Type
    deriving (Show, Eq)

data MetallicComposeStmt
    = MCBind String MetallicExpr
    | MCLet String MetallicExpr
    | MCExpr MetallicExpr
    deriving (Show, Eq)

data MCaseArm = MCaseArm
    { mcaPatterns :: [Pattern]
    , mcaBody :: MetallicExpr
    }
    deriving (Show, Eq)

data MetallicLiteral
    = MInt Int
    | MBool Bool
    | MString String
    deriving (Show, Eq)

data MetallicStatement
    = MAssign String MetallicExpr
    | MStore MetallicExpr MetallicExpr
    deriving (Show, Eq)

getMetallicExprType :: MetallicExpr -> Type
getMetallicExprType (MVar _ t) = t
getMetallicExprType (MLit lit) = getMetallicLiteralType lit
getMetallicExprType (MCall _ _ t) = t
getMetallicExprType (MTypeApp _ _ t) = t
getMetallicExprType (MLet _ _ _ t) = t
getMetallicExprType (MIf _ _ _ t) = t
getMetallicExprType (MLambda _ _ t) = t
getMetallicExprType (MConstruct _ _ _ t) = t
getMetallicExprType (MArrayLit _ t) = t
getMetallicExprType (MTuple _ t) = t
getMetallicExprType (MCase _ _ _ t) = t
getMetallicExprType (MFieldAccess _ _ t) = t
getMetallicExprType (MPanic _ t) = t
getMetallicExprType (MCompose _ t) = t

getMetallicLiteralType :: MetallicLiteral -> Type
getMetallicLiteralType (MInt _) = intType
getMetallicLiteralType (MBool _) = boolType
getMetallicLiteralType (MString _) = strType
