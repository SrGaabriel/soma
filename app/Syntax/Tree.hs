module Syntax.Tree (Expr (..), exprChildren, exprSpan, modifySpan, uncurryApp) where

import Lexing.Position (Span (..))
import Project.Symbols (Symbol)
import Syntax.Patterns (Pattern (..))
import Typing.Types (Constraint, Kind, QualifiedType, TyVar, Type)

data Expr
    = ExprRoot [Expr]
    | ExprNum String Span
    | ExprStr String Span
    | ExprUVar String Span
    | ExprVar Symbol Span
    | ExprBool Bool Span
    | ExprBlock [Expr] Span
    | ExprArray [Expr] Span
    | ExprTuple [Expr] Span
    | ExprApp Expr Expr
    | ExprLambda [String] Expr Span
    | ExprImport String Span
    | ExprPatternMatch Expr [Expr] Span
    | ExprDerivedPatternMatch [Expr]
    | ExprPatternMatchArm
        { patternMatchArmPatterns :: [Pattern]
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
    | ExprIntrinsicDef
        { intrinsicName :: String
        , intrinsicType :: QualifiedType
        , intrinsicSpan :: Span
        }
    | ExprDataTypeDef
        { dataName :: String
        , dataGenerics :: [TyVar]
        , dataConstraints :: [Constraint]
        , dataConstructors :: [Expr]
        , dataSpan :: Span
        }
    | ExprIntrinsicDataTypeDef
        { intrinsicDataTypeName :: String
        , intrinsicDataTypeKind :: Kind
        , intrinsicDataTypeSpan :: Span
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
        { instanceConstraint :: Type
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
exprChildren (ExprPatternMatchArm _ body _) = [body]
exprChildren (ExprDataConstructor{}) = []
exprChildren (ExprImport _ _) = []
exprChildren (ExprNum _ _) = []
exprChildren (ExprStr _ _) = []
exprChildren (ExprUVar _ _) = []
exprChildren (ExprVar{}) = []
exprChildren (ExprBool _ _) = []
exprChildren (ExprTypeClassBinding _ _ (Just impl) _) = impl
exprChildren (ExprTypeClassBinding _ _ Nothing _) = []
exprChildren (ExprDerivedPatternMatch arms) = arms
exprChildren (ExprBindingDef _ _ body _ _) = [body]
exprChildren (ExprIntrinsicDef{}) = []
exprChildren (ExprDataTypeDef _ _ _ constructors _) = constructors
exprChildren (ExprIntrinsicDataTypeDef{}) = []
exprChildren (ExprTypeClassDef _ _ methods _) = methods
exprChildren (ExprInstanceDef _ methods _) = methods

exprSpan :: Expr -> Span
exprSpan (ExprRoot _) = error "Root expressions do not have a span"
exprSpan (ExprNum _ s) = s
exprSpan (ExprStr _ s) = s
exprSpan (ExprUVar _ s) = s
exprSpan (ExprVar _ s) = s
exprSpan (ExprBool _ s) = s
exprSpan (ExprBlock _ s) = s
exprSpan (ExprArray _ s) = s
exprSpan (ExprTuple _ s) = s
exprSpan (ExprApp first second) = spanningExprs [first, second]
exprSpan (ExprLambda _ _ s) = s
exprSpan (ExprLet _ _ _ s) = s
exprSpan (ExprBindingDef _ _ _ _ s) = s
exprSpan (ExprIntrinsicDef _ _ s) = s
exprSpan (ExprDataTypeDef _ _ _ _ s) = s
exprSpan (ExprIntrinsicDataTypeDef _ _ s) = s
exprSpan (ExprDataConstructor _ _ s) = s
exprSpan (ExprTypeClassDef _ _ _ s) = s
exprSpan (ExprTypeClassBinding _ _ _ s) = s
exprSpan (ExprPatternMatch _ _ s) = s
exprSpan (ExprDerivedPatternMatch arms) = spanningExprs arms
exprSpan (ExprPatternMatchArm _ _ s) = s
exprSpan (ExprInstanceDef _ _ s) = s
exprSpan (ExprImport _ s) = s

modifySpan :: Expr -> Span -> Expr
modifySpan e@(ExprRoot _) _ = e
modifySpan (ExprNum n _) s = ExprNum n s
modifySpan (ExprStr s _) newSpan = ExprStr s newSpan
modifySpan (ExprUVar v _) newSpan = ExprUVar v newSpan
modifySpan (ExprVar sym _) newSpan = ExprVar sym newSpan
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
modifySpan (ExprIntrinsicDef name typ _) newSpan =
    ExprIntrinsicDef name typ newSpan
modifySpan (ExprDataTypeDef name generics constraints constructors _) newSpan =
    ExprDataTypeDef name generics constraints constructors newSpan
modifySpan (ExprIntrinsicDataTypeDef name kind _) newSpan =
    ExprIntrinsicDataTypeDef name kind newSpan
modifySpan (ExprDataConstructor name args _) newSpan =
    ExprDataConstructor name args newSpan
modifySpan (ExprTypeClassDef name generics bindings _) newSpan =
    ExprTypeClassDef name generics bindings newSpan
modifySpan (ExprTypeClassBinding name bindType defaultImpl _) newSpan =
    ExprTypeClassBinding name bindType defaultImpl newSpan
modifySpan (ExprPatternMatch expr arms _) newSpan =
    ExprPatternMatch expr arms newSpan
modifySpan e@(ExprDerivedPatternMatch _) _ = e
modifySpan (ExprPatternMatchArm patterns body _) newSpan =
    ExprPatternMatchArm patterns body newSpan
modifySpan (ExprInstanceDef constraintType methods _) newSpan =
    ExprInstanceDef constraintType methods newSpan
modifySpan (ExprImport moduleName _) newSpan =
    ExprImport moduleName newSpan

spanningExprs :: [Expr] -> Span
spanningExprs [] = error "Cannot create a span from an empty list of expressions"
spanningExprs exprs =
    let spans = map exprSpan exprs
        leftmostStart = minimum $ map (\(Span start _) -> start) spans
        rightmostEnd = maximum $ map (\(Span _ end) -> end) spans
    in Span leftmostStart rightmostEnd

-- returns the base (first non-app expression) and a list of arguments
uncurryApp :: Expr -> (Expr, [Expr])
uncurryApp (ExprApp f arg) =
    let (base, args) = uncurryApp f
    in (base, args ++ [arg])
uncurryApp base = (base, [])
