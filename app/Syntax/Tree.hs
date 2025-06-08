module Syntax.Tree where

import Lexing.Position (Span)
import Syntax.Ops (BinaryOp)
import Typing.Types (Type)

data Expr
    = ExprRoot [Expr]
    | ExprNum String Span
    | ExprStr String Span
    | ExprVar String Span
    | ExprBool Bool Span
    | ExprBlock [Expr] Span
    | ExprArray [Expr] Span
    | ExprTuple [Expr] Span
    | ExprApp Expr Expr
    | ExprLambda [String] Expr Span
    | ExprBinaryOp BinaryOp Expr Expr
    | ExprLet
        { letName :: String
        , letValue :: Expr
        , letBody :: Expr
        , letSpan :: Span
        }
    | ExprFunctionDef
        { functionName :: String
        , functionArgs :: [(String, Type)]
        , functionReturnType :: Type
        , functionBody :: Expr
        , functionSpan :: Span
        }
    | ExprConstantDef
        { constantName :: String
        , constantType :: Type
        , constantValue :: Expr
        , constantSpan :: Span
        }
    deriving (Show, Eq, Ord)

exprChildren :: Expr -> [Expr]
exprChildren (ExprRoot exprs) = exprs
exprChildren (ExprBlock exprs _) = exprs
exprChildren (ExprArray exprs _) = exprs
exprChildren (ExprTuple exprs _) = exprs
exprChildren (ExprApp f arg) = [f, arg]
exprChildren (ExprLambda _ body _) = [body]
exprChildren (ExprBinaryOp _ left right) = [left, right]
exprChildren _ = []