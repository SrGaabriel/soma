module Syntax.Tree where

import Lexing.Position (Span)
import Syntax.Ops (BinaryOp)
import Typing.Types (TyVar, Type)

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
    | ExprStructDef
        { structName :: String
        , structGenerics :: [TyVar]
        , structConstructors :: [Expr]
        , structSpan :: Span
        }
    | ExprStructConstructor
        { structConstructorName :: String
        , structConstructorArgs :: [(String, Type)]
        , structConstructorSpan :: Span
        }
    | ExprTypeClassDef
        { typeClassName :: String
        , typeClassGenerics :: [TyVar]
        , typeClassMethods :: [Expr]
        , typeClassSpan :: Span
        }
    | ExprTypeClassMethod
        { typeClassMethodName :: String
        , typeClassMethodArgs :: [(String, Type)]
        , typeClassMethodReturnType :: Type
        , typeClassMethodDefaultImpl :: Maybe [Expr]
        , typeClassMethodSpan :: Span
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
exprChildren (ExprLet _ value body _) = [value, body]
exprChildren (ExprFunctionDef _ _ _ body _) = [body]
exprChildren (ExprConstantDef _ _ value _) = [value]
exprChildren (ExprStructDef _ _ constructors _) = constructors
exprChildren (ExprTypeClassDef _ _ methods _) = methods
exprChildren (ExprTypeClassMethod _ _ _ (Just impl) _) = impl
exprChildren _ = []
