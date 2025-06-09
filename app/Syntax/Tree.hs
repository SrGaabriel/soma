module Syntax.Tree where

import Lexing.Position (Span (..))
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

exprSpan :: Expr -> Span
exprSpan (ExprRoot _) = error "Root expressions do not have a span"
exprSpan (ExprNum _ s) = s
exprSpan (ExprStr _ s) = s
exprSpan (ExprVar _ s) = s
exprSpan (ExprBool _ s) = s
exprSpan (ExprBlock _ s) = s
exprSpan (ExprArray _ s) = s
exprSpan (ExprTuple _ s) = s
exprSpan (ExprApp first second) = 
    let Span start _ = exprSpan first
        Span _ end = exprSpan second
    in Span start end
exprSpan (ExprLambda _ _ s) = s
exprSpan (ExprBinaryOp _ first second) =
    let Span start _ = exprSpan first
        Span _ end = exprSpan second
    in Span start end
exprSpan (ExprLet _ _ _ s) = s
exprSpan (ExprFunctionDef _ _ _ _ s) = s
exprSpan (ExprConstantDef _ _ _ s) = s
exprSpan (ExprStructDef _ _ _ s) = s
exprSpan (ExprStructConstructor _ _ s) = s
exprSpan (ExprTypeClassDef _ _ _ s) = s
exprSpan (ExprTypeClassMethod _ _ _ _ s) = s