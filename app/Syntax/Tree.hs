module Syntax.Tree (Expr (..), SinglePatternArm (..), MultiPatternArm (..), exprChildren, exprSpan) where

import Lexing.Position (Span (..))
import Syntax.Patterns (Pattern (..))
import Typing.Types (Constraint, QualifiedType, TyVar, Type)
import Utils.Lists (hardHead)

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
    | ExprPatternMatch Expr [SinglePatternArm] Span
    | ExprDerivedPatternMatch [QualifiedType] [MultiPatternArm]
    | ExprLet
        { letName :: String
        , letValue :: Expr
        , letBody :: Expr
        , letSpan :: Span
        }
    | ExprBindingDef
        { bindingName :: String
        , bindingType :: QualifiedType
        , bindingBody :: Expr
        , bindingIsImpl :: Bool
        , bindingSpan :: Span
        }
    | ExprDataTypeDef
        { dataName :: String
        , dataGenerics :: [TyVar]
        , dataConstraints :: [Constraint]
        , dataConstructors :: [Expr]
        , dataSpan :: Span
        }
    | ExprDataConstructor
        { structConstructorName :: String
        , structConstructorArgs :: [(String, Type)]
        , structConstructorSpan :: Span
        }
    | ExprTypeClassDef
        { typeClassName :: String
        , typeClassGenerics :: [TyVar]
        , typeClassBindings :: [Expr]
        , typeClassSpan :: Span
        }
    | ExprTypeClassBinding
        { typeClassBindName :: String
        , typeClassBindType :: QualifiedType
        , typeClassBindDefaultImpl :: Maybe [Expr]
        , typeClassBindSpan :: Span
        }
    | ExprInstanceDef
        { instanceClassName :: String
        , instanceDataTypeName :: String -- todo: change this to a single qualified type
        , instanceMethods :: [Expr]
        , instanceSpan :: Span
        }
    deriving (Show, Eq, Ord)

data SinglePatternArm = SinglePatternArm Pattern Expr deriving (Show, Eq, Ord)
data MultiPatternArm = MultiPatternArm [Pattern] Expr deriving (Show, Eq, Ord)

exprChildren :: Expr -> [Expr]
exprChildren (ExprRoot exprs) = exprs
exprChildren (ExprBlock exprs _) = exprs
exprChildren (ExprArray exprs _) = exprs
exprChildren (ExprTuple exprs _) = exprs
exprChildren (ExprApp f arg) = [f, arg]
exprChildren (ExprLambda _ body _) = [body]
exprChildren (ExprLet _ value body _) = [value, body]
exprChildren (ExprPatternMatch expr arms _) = expr : map (\(SinglePatternArm _ arm) -> arm) arms
exprChildren (ExprDerivedPatternMatch _ arms) = map (\(MultiPatternArm _ arm) -> arm) arms
exprChildren (ExprBindingDef _ _ body _ _) = [body]
exprChildren (ExprDataTypeDef _ _ _ constructors _) = constructors
exprChildren (ExprTypeClassDef _ _ methods _) = methods
exprChildren (ExprTypeClassBinding _ _ (Just impl) _) = impl
exprChildren (ExprInstanceDef _ _ methods _) = methods
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
exprSpan (ExprLet _ _ _ s) = s
exprSpan (ExprBindingDef _ _ _ _ s) = s
exprSpan (ExprDataTypeDef _ _ _ _ s) = s
exprSpan (ExprDataConstructor _ _ s) = s
exprSpan (ExprTypeClassDef _ _ _ s) = s
exprSpan (ExprTypeClassBinding _ _ _ s) = s
exprSpan (ExprPatternMatch _ _ s) = s
exprSpan (ExprDerivedPatternMatch _ arms) =
    let spans = map (\(MultiPatternArm _ arm) -> exprSpan arm) arms
    in case spans of
        [] -> error "Derived pattern match arms cannot be empty"
        _ ->
            let Span start _ = hardHead spans
                Span _ end = last spans
            in Span start end
exprSpan (ExprInstanceDef _ _ _ s) = s
