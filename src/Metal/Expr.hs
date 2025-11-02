module Metal.Expr where

import Typing.Types (Type)

data MetallicExpr
    = MVar String Type
    | MLit MetallicLiteral
    | MApp String [MetallicExpr] Type
    | MPolyApp String [Type] [MetallicExpr] Type
    | MLet String MetallicExpr MetallicExpr Type
    | MConstruct String Int [MetallicExpr] Type
    | MArrayLit [MetallicExpr] Type
    | MIndirectCall MetallicExpr [MetallicExpr] Type
    deriving (Show, Eq)

data MetallicLiteral
    = MInt Integer
    | MBool Bool
    | MFloat Double
    | MString String
    deriving (Show, Eq)

data MetallicStatement
    = MAssign String MetallicExpr
    | MStore MetallicExpr MetallicExpr
    deriving (Show)