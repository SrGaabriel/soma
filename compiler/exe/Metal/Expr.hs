{-# LANGUAGE FlexibleInstances #-}

module Metal.Expr where

import Syntax.Patterns (Pattern)
import Typing.Types (Type, boolType, intType, strType)

class HasType a where
    getType :: a -> Type

instance HasType MetallicExpr where
    getType (MVar _ t) = t
    getType (MLit lit) = getType lit
    getType (MCall _ _ t) = t
    getType (MTypeApp _ _ t) = t
    getType (MLet _ _ _ t) = t
    getType (MIf _ _ _ t) = t
    getType (MLambda _ _ t) = t
    getType (MClosure _ _ t) = t
    getType (MConstruct _ _ _ t) = t
    getType (MArrayLit _ t) = t
    getType (MTuple _ t) = t
    getType (MCase _ _ _ t) = t
    getType (MFieldAccess _ _ t) = t
    getType (MPanic _ t) = t
    getType (MCompose _ t) = t

instance HasType MetallicLiteral where
    getType (MInt _) = intType
    getType (MBool _) = boolType
    getType (MString _) = strType

data MetallicExpr
    = MVar String Type
    | MLit MetallicLiteral
    | MCall MetallicExpr [MetallicExpr] Type
    | MTypeApp MetallicExpr [Type] Type
    | MLet String MetallicExpr MetallicExpr Type
    | MLambda [String] MetallicExpr Type
    | {- | MClosure liftedFuncName capturedVars closureType
      Represents a closure: a lifted function + captured environment
      -}
      MClosure String [(String, Type)] Type
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
getMetallicExprType = getType

getMetallicLiteralType :: MetallicLiteral -> Type
getMetallicLiteralType = getType
