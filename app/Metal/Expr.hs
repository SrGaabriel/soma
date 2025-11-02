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

data MetallicTypeDef
    = MAlgebraicType
        { mtName :: String
        , mtConstructors :: [MetallicConstructor]
        }
    | MRecordType
        { mrName :: String
        , mrFields :: [(String, Type)]
        }

data MetallicConstructor = MetallicConstructor
    { mcName :: String
    , mcTag :: Int
    , mcFields :: [Type]
    }

data MetallicStatement
    = MAssign String MetallicExpr
    | MStore MetallicExpr MetallicExpr
    deriving (Show)

data MetallicLiteral
    = MInt Integer
    | MBool Bool
    | MFloat Double
    | MString String
    deriving (Show, Eq)