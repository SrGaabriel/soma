module Syntax.Tree (Expr (..), exprChildren, exprSpan, modifySpan) where

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
    | ExprImport String Span
    | ExprPatternMatch Expr [Expr] Span
    | ExprDerivedPatternMatch [QualifiedType] [Expr]
    | ExprPatternMatchArm
        { patternMatchArmPatterns :: [Pattern]
        , patternMatchArmTypes :: [QualifiedType]
        , patternMatchArmBody :: Expr
        , patternMatchArmSpan :: Span
        }
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

exprChildren :: Expr -> [Expr]
exprChildren (ExprRoot exprs) = exprs
exprChildren (ExprBlock exprs _) = exprs
exprChildren (ExprArray exprs _) = exprs
exprChildren (ExprTuple exprs _) = exprs
exprChildren (ExprApp f arg) = [f, arg]
exprChildren (ExprLambda _ body _) = [body]
exprChildren (ExprLet _ value body _) = [value, body]
exprChildren (ExprPatternMatch expr arms _) = expr : arms
exprChildren (ExprDerivedPatternMatch _ arms) = arms
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
    let spans = map exprSpan arms
    in case spans of
        [] -> error "Derived pattern match arms cannot be empty"
        _ ->
            let Span start _ = hardHead spans
                Span _ end = last spans
            in Span start end
exprSpan (ExprPatternMatchArm _ _ _ s) = s
exprSpan (ExprInstanceDef _ _ _ s) = s
exprSpan (ExprImport _ s) = s

modifySpan :: Expr -> Span -> Expr
modifySpan e@(ExprRoot _) _ = e
modifySpan (ExprNum n _) s = ExprNum n s
modifySpan (ExprStr s _) newSpan = ExprStr s newSpan
modifySpan (ExprVar v _) newSpan = ExprVar v newSpan
modifySpan (ExprBool b _) newSpan = ExprBool b newSpan
modifySpan (ExprBlock exprs _) newSpan = ExprBlock exprs newSpan
modifySpan (ExprArray exprs _) newSpan = ExprArray exprs newSpan
modifySpan (ExprTuple exprs _) newSpan = ExprTuple exprs newSpan
modifySpan (ExprApp f arg) newSpan =
    let Span _fStart fEnd = exprSpan f
        Span argStart _argEnd = exprSpan arg
        Span newStart newEnd = newSpan
    in ExprApp (modifySpan f (Span newStart fEnd)) (modifySpan arg (Span argStart newEnd))
modifySpan (ExprLambda args body _) newSpan =
    ExprLambda args body newSpan
modifySpan (ExprLet name value body _) newSpan =
    ExprLet name value body newSpan
modifySpan (ExprBindingDef name bindType body isImpl _) newSpan =
    ExprBindingDef name bindType body isImpl newSpan
modifySpan (ExprDataTypeDef name generics constraints constructors _) newSpan =
    ExprDataTypeDef name generics constraints constructors newSpan
modifySpan (ExprDataConstructor name args _) newSpan =
    ExprDataConstructor name args newSpan
modifySpan (ExprTypeClassDef name generics bindings _) newSpan =
    ExprTypeClassDef name generics bindings newSpan
modifySpan (ExprTypeClassBinding name bindType defaultImpl _) newSpan =
    ExprTypeClassBinding name bindType defaultImpl newSpan
modifySpan (ExprPatternMatch expr arms _) newSpan =
    ExprPatternMatch expr arms newSpan
modifySpan e@(ExprDerivedPatternMatch _ _) _ = e
modifySpan (ExprPatternMatchArm patterns types body _) newSpan =
    ExprPatternMatchArm patterns types body newSpan
modifySpan (ExprInstanceDef className dataTypeName methods _) newSpan =
    ExprInstanceDef className dataTypeName methods newSpan
modifySpan (ExprImport moduleName _) newSpan =
    ExprImport moduleName newSpan
