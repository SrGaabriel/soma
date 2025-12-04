module Syntax.Tree (Expr (..), Modifier (..), exprChildren, exprSpan, modifySpan, uncurryApp, ComposeStmt (..)) where

import Lexing.Position (Located (..), Span (..))
import Project.Symbols (Symbol)
import Syntax.Patterns (Pattern (..))
import Typing.Types (Constraint, Kind, QualifiedType, TyVar, Type)

data Modifier
    = ModInline
    deriving (Show, Eq, Ord)

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
    | ExprImport String [String] Span
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
        , bindingType :: Located QualifiedType
        , bindingBody :: Expr
        , bindingIsImpl :: Bool
        , bindingModifiers :: [Modifier]
        , bindingSpan :: Span
        }
    | ExprIntrinsicDef
        { intrinsicName :: String
        , intrinsicType :: Located QualifiedType
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
        , structConstructorArgs :: [(String, Located Type)]
        , structConstructorSpan :: Span
        }
    | ExprTypeClassDef
        { typeClassName :: String
        , typeClassType :: Located QualifiedType
        , typeClassBindings :: [Expr]
        , typeClassSpan :: Span
        }
    | ExprTypeClassBinding
        { typeClassBindName :: String
        , typeClassBindType :: Located QualifiedType
        , typeClassBindDefaultImpl :: Maybe [Expr]
        , typeClassBindSpan :: Span
        }
    | ExprInstanceDef
        { instanceConstraint :: QualifiedType
        , instanceMethods :: [Expr]
        , instanceSpan :: Span
        }
    | ExprIf
        { ifCondition :: Expr
        , ifBody :: Expr
        , ifElseBody :: Expr
        , ifSpan :: Span
        }
    | ExprCompose [ComposeStmt] Span
    deriving (Show, Eq, Ord)

data ComposeStmt
    = CSBind String Expr Span
    | CSLet String Expr Span
    | CSExpr Expr Span
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
exprChildren (ExprImport{}) = []
exprChildren (ExprNum _ _) = []
exprChildren (ExprStr _ _) = []
exprChildren (ExprUVar _ _) = []
exprChildren (ExprVar{}) = []
exprChildren (ExprBool _ _) = []
exprChildren (ExprTypeClassBinding _ _ (Just impl) _) = impl
exprChildren (ExprTypeClassBinding _ _ Nothing _) = []
exprChildren (ExprDerivedPatternMatch arms) = arms
exprChildren (ExprBindingDef _ _ body _ _ _) = [body]
exprChildren (ExprIntrinsicDef{}) = []
exprChildren (ExprDataTypeDef _ _ _ constructors _) = constructors
exprChildren (ExprIntrinsicDataTypeDef{}) = []
exprChildren (ExprTypeClassDef _ _ methods _) = methods
exprChildren (ExprInstanceDef _ methods _) = methods
exprChildren (ExprCompose stmts _) = concatMap stmtChildren stmts
exprChildren (ExprIf cond ifBlock elseBlock _) = [cond, ifBlock, elseBlock]

stmtChildren :: ComposeStmt -> [Expr]
stmtChildren (CSBind _ e _) = [e]
stmtChildren (CSLet _ e _) = [e]
stmtChildren (CSExpr e _) = [e]

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
exprSpan (ExprBindingDef _ _ _ _ _ s) = s
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
exprSpan (ExprImport _ _ s) = s
exprSpan (ExprCompose _ s) = s
exprSpan (ExprIf _ _ _ s) = s

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
modifySpan (ExprBindingDef name bindType body isImpl mods _) newSpan =
    ExprBindingDef name bindType body isImpl mods newSpan
modifySpan (ExprIntrinsicDef name typ _) newSpan =
    ExprIntrinsicDef name typ newSpan
modifySpan (ExprDataTypeDef name generics constraints constructors _) newSpan =
    ExprDataTypeDef name generics constraints constructors newSpan
modifySpan (ExprIntrinsicDataTypeDef name kind _) newSpan =
    ExprIntrinsicDataTypeDef name kind newSpan
modifySpan (ExprDataConstructor name args _) newSpan =
    ExprDataConstructor name args newSpan
modifySpan (ExprTypeClassDef name ty bindings _) newSpan =
    ExprTypeClassDef name ty bindings newSpan
modifySpan (ExprTypeClassBinding name bindType defaultImpl _) newSpan =
    ExprTypeClassBinding name bindType defaultImpl newSpan
modifySpan (ExprPatternMatch expr arms _) newSpan =
    ExprPatternMatch expr arms newSpan
modifySpan e@(ExprDerivedPatternMatch _) _ = e
modifySpan (ExprPatternMatchArm patterns body _) newSpan =
    ExprPatternMatchArm patterns body newSpan
modifySpan (ExprInstanceDef constraintType methods _) newSpan =
    ExprInstanceDef constraintType methods newSpan
modifySpan (ExprImport moduleName elements _) newSpan =
    ExprImport moduleName elements newSpan
modifySpan (ExprCompose stmts _) newSpan =
    ExprCompose stmts newSpan
modifySpan (ExprIf cond ifBlock elseBlock _) newSpan =
    ExprIf cond ifBlock elseBlock newSpan

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
