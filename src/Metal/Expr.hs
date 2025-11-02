module Metal.Expr where

import qualified Decisions.Model as DAG
import Typing.Types (Type, boolType, intType, strType)

data MetallicExpr
    = MVar String Type
    | MLit MetallicLiteral
    | MApp String [MetallicExpr] Type
    | MPolyApp String [Type] [MetallicExpr] Type
    | MLet String MetallicExpr MetallicExpr Type
    | MConstruct String Int [MetallicExpr] Type
    | MArrayLit [MetallicExpr] Type
    | MIndirectCall MetallicExpr [MetallicExpr] Type
    | MSwitch MetallicExpr [(DAG.Constructor, MetallicExpr)] (Maybe MetallicExpr) Type
    | MFieldAccess MetallicExpr Int Type
    | MPanic String Type
    deriving (Show, Eq)

data MetallicLiteral
    = MInt Integer
    | MBool Bool
    | MString String
    deriving (Show, Eq)

data MetallicStatement
    = MAssign String MetallicExpr
    | MStore MetallicExpr MetallicExpr
    deriving (Show)

getMetallicExprType :: MetallicExpr -> Type
getMetallicExprType (MVar _ t) = t
getMetallicExprType (MLit lit) = getMetallicLiteralType lit
getMetallicExprType (MApp _ _ t) = t
getMetallicExprType (MPolyApp _ _ _ t) = t
getMetallicExprType (MLet _ _ _ t) = t
getMetallicExprType (MConstruct _ _ _ t) = t
getMetallicExprType (MArrayLit _ t) = t
getMetallicExprType (MIndirectCall _ _ t) = t
getMetallicExprType (MSwitch _ _ _ t) = t
getMetallicExprType (MFieldAccess _ _ t) = t
getMetallicExprType (MPanic _ t) = t

getMetallicLiteralType :: MetallicLiteral -> Type
getMetallicLiteralType (MInt _) = intType
getMetallicLiteralType (MBool _) = boolType
getMetallicLiteralType (MString _) = strType
