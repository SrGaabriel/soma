{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Metal.Expr (
    Phase (..),
    MetallicExpr (..),
    MCaseArm (..),
    TypedPattern (..),
    typedPatternSpan,
    typedPatternType,
    MetallicLiteral (..),
    MetallicStatement (..),
    TypeSlot (..),
    slotToType,
    XType,
    XVar,
    XCall,
    XTypeApp,
    XLet,
    XLambda,
    XLambdaParams,
    XClosure,
    XClosureCaptures,
    XConstruct,
    XArrayLit,
    XTuple,
    XIf,
    XCase,
    XFieldAccess,
    XPanic,
    XCaseArmPatterns,
    UntypedExpr,
    TypedExpr,
    InferenceExpr,
    UntypedArm,
    TypedArm,
    InferenceArm,
    HasType (..),
    literalType,
    inferenceSlot,
    exprSpan,
) where

import Lexing.Position (Span)
import Project.Name (Name)
import Syntax.Patterns (Literal, ResolvedPattern)
import Typing.Types (TyVar (..), Type (..), boolType, intType, strType)

data TypedPattern
    = TPVar Name Type Span
    | TPWildcard Type Span
    | TPLit Literal Type Span
    | TPConstructor Name [TypedPattern] Type Span
    | TPTuple [TypedPattern] Type Span
    | TPArray [TypedPattern] Type Span
    | TPAs Name TypedPattern Type Span
    deriving (Show, Eq)

typedPatternSpan :: TypedPattern -> Span
typedPatternSpan (TPVar _ _ s) = s
typedPatternSpan (TPWildcard _ s) = s
typedPatternSpan (TPLit _ _ s) = s
typedPatternSpan (TPConstructor _ _ _ s) = s
typedPatternSpan (TPTuple _ _ s) = s
typedPatternSpan (TPArray _ _ s) = s
typedPatternSpan (TPAs _ _ _ s) = s

typedPatternType :: TypedPattern -> Type
typedPatternType (TPVar _ t _) = t
typedPatternType (TPWildcard t _) = t
typedPatternType (TPLit _ t _) = t
typedPatternType (TPConstructor _ _ t _) = t
typedPatternType (TPTuple _ t _) = t
typedPatternType (TPArray _ t _) = t
typedPatternType (TPAs _ _ t _) = t

data Phase = Untyped | Inference | Typed

data TypeSlot
    = Known Type
    | Hole TyVar
    deriving (Show, Eq, Ord)

slotToType :: TypeSlot -> Type
slotToType (Known t) = t
slotToType (Hole tv) = TVar tv

type family XType (p :: Phase) where
    XType Untyped = ()
    XType Inference = TypeSlot
    XType Typed = Type

type family XVar (p :: Phase) where
    XVar Untyped = ()
    XVar Inference = TypeSlot
    XVar Typed = Type

type family XCall (p :: Phase) where
    XCall Untyped = ()
    XCall Inference = TypeSlot
    XCall Typed = Type

type family XTypeApp (p :: Phase) where
    XTypeApp Untyped = ()
    XTypeApp Inference = TypeSlot
    XTypeApp Typed = Type

type family XLet (p :: Phase) where
    XLet Untyped = ()
    XLet Inference = TypeSlot
    XLet Typed = Type

type family XLambda (p :: Phase) where
    XLambda Untyped = ()
    XLambda Inference = TypeSlot
    XLambda Typed = Type

type family XLambdaParams (p :: Phase) where
    XLambdaParams Untyped = [Name]
    XLambdaParams Inference = [(Name, TypeSlot)]
    XLambdaParams Typed = [(Name, Type)]

type family XClosure (p :: Phase) where
    XClosure Untyped = ()
    XClosure Inference = TypeSlot
    XClosure Typed = Type

type family XClosureCaptures (p :: Phase) where
    XClosureCaptures Untyped = [Name]
    XClosureCaptures Inference = [(Name, TypeSlot)]
    XClosureCaptures Typed = [(Name, Type)]

type family XConstruct (p :: Phase) where
    XConstruct Untyped = ()
    XConstruct Inference = TypeSlot
    XConstruct Typed = Type

type family XArrayLit (p :: Phase) where
    XArrayLit Untyped = ()
    XArrayLit Inference = TypeSlot
    XArrayLit Typed = Type

type family XTuple (p :: Phase) where
    XTuple Untyped = ()
    XTuple Inference = TypeSlot
    XTuple Typed = Type

type family XIf (p :: Phase) where
    XIf Untyped = ()
    XIf Inference = TypeSlot
    XIf Typed = Type

type family XCase (p :: Phase) where
    XCase Untyped = ()
    XCase Inference = TypeSlot
    XCase Typed = Type

type family XFieldAccess (p :: Phase) where
    XFieldAccess Untyped = ()
    XFieldAccess Inference = TypeSlot
    XFieldAccess Typed = Type

type family XPanic (p :: Phase) where
    XPanic Untyped = ()
    XPanic Inference = TypeSlot
    XPanic Typed = Type

type family XCaseArmPatterns (p :: Phase) where
    XCaseArmPatterns Untyped = [ResolvedPattern]
    XCaseArmPatterns Inference = [ResolvedPattern] -- Patterns typed during applySubstitution
    XCaseArmPatterns Typed = [TypedPattern]

data MetallicExpr (p :: Phase)
    = MVar Name (XVar p) Span
    | MLit MetallicLiteral Span
    | MCall (MetallicExpr p) [MetallicExpr p] (XCall p) Span
    | MTypeApp (MetallicExpr p) [Type] (XTypeApp p) Span
    | MLet Name (MetallicExpr p) (MetallicExpr p) (XLet p) Span
    | MLambda (XLambdaParams p) (MetallicExpr p) (XLambda p) Span
    | MClosure Name (XClosureCaptures p) (XClosure p) Span
    | MConstruct Name Int [MetallicExpr p] (XConstruct p) Span
    | MArrayLit [MetallicExpr p] (XArrayLit p) Span
    | MTuple [MetallicExpr p] (XTuple p) Span
    | MIf (MetallicExpr p) (MetallicExpr p) (MetallicExpr p) (XIf p) Span
    | MCase [MetallicExpr p] [MCaseArm p] (Maybe (MetallicExpr p)) (XCase p) Span
    | MFieldAccess (MetallicExpr p) Int (XFieldAccess p) Span
    | MPanic String (XPanic p) Span

deriving instance
    ( Show (XVar p)
    , Show (XCall p)
    , Show (XTypeApp p)
    , Show (XLet p)
    , Show (XLambda p)
    , Show (XLambdaParams p)
    , Show (XClosure p)
    , Show (XClosureCaptures p)
    , Show (XConstruct p)
    , Show (XArrayLit p)
    , Show (XTuple p)
    , Show (XIf p)
    , Show (XCase p)
    , Show (XFieldAccess p)
    , Show (XPanic p)
    , Show (XCaseArmPatterns p)
    ) =>
    Show (MetallicExpr p)

deriving instance
    ( Eq (XVar p)
    , Eq (XCall p)
    , Eq (XTypeApp p)
    , Eq (XLet p)
    , Eq (XLambda p)
    , Eq (XLambdaParams p)
    , Eq (XClosure p)
    , Eq (XClosureCaptures p)
    , Eq (XConstruct p)
    , Eq (XArrayLit p)
    , Eq (XTuple p)
    , Eq (XIf p)
    , Eq (XCase p)
    , Eq (XFieldAccess p)
    , Eq (XPanic p)
    , Eq (XCaseArmPatterns p)
    ) =>
    Eq (MetallicExpr p)

data MCaseArm (p :: Phase) = MCaseArm
    { mcaPatterns :: XCaseArmPatterns p
    , mcaBody :: MetallicExpr p
    }

deriving instance (Show (XCaseArmPatterns p), Show (MetallicExpr p)) => Show (MCaseArm p)

deriving instance (Eq (XCaseArmPatterns p), Eq (MetallicExpr p)) => Eq (MCaseArm p)

data MetallicLiteral
    = MInt Int
    | MBool Bool
    | MString String
    deriving (Show, Eq)

data MetallicStatement
    = MAssign Name (MetallicExpr Typed)
    | MStore (MetallicExpr Typed) (MetallicExpr Typed)

deriving instance Show MetallicStatement

deriving instance Eq MetallicStatement

type UntypedExpr = MetallicExpr Untyped

type InferenceExpr = MetallicExpr Inference

type TypedExpr = MetallicExpr Typed

type UntypedArm = MCaseArm Untyped

type InferenceArm = MCaseArm Inference

type TypedArm = MCaseArm Typed

exprSpan :: MetallicExpr p -> Span
exprSpan (MVar _ _ s) = s
exprSpan (MLit _ s) = s
exprSpan (MCall _ _ _ s) = s
exprSpan (MTypeApp _ _ _ s) = s
exprSpan (MLet _ _ _ _ s) = s
exprSpan (MLambda _ _ _ s) = s
exprSpan (MClosure _ _ _ s) = s
exprSpan (MConstruct _ _ _ _ s) = s
exprSpan (MArrayLit _ _ s) = s
exprSpan (MTuple _ _ s) = s
exprSpan (MIf _ _ _ _ s) = s
exprSpan (MCase _ _ _ _ s) = s
exprSpan (MFieldAccess _ _ _ s) = s
exprSpan (MPanic _ _ s) = s

literalType :: MetallicLiteral -> Type
literalType (MInt _) = intType
literalType (MBool _) = boolType
literalType (MString _) = strType

class HasType a where
    getType :: a -> Type

instance HasType TypedExpr where
    getType (MVar _ t _) = t
    getType (MLit lit _) = literalType lit
    getType (MCall _ _ t _) = t
    getType (MTypeApp _ _ t _) = t
    getType (MLet _ _ _ t _) = t
    getType (MIf _ _ _ t _) = t
    getType (MLambda _ _ t _) = t
    getType (MClosure _ _ t _) = t
    getType (MConstruct _ _ _ t _) = t
    getType (MArrayLit _ t _) = t
    getType (MTuple _ t _) = t
    getType (MCase _ _ _ t _) = t
    getType (MFieldAccess _ _ t _) = t
    getType (MPanic _ t _) = t

instance HasType MetallicLiteral where
    getType = literalType

inferenceSlot :: InferenceExpr -> TypeSlot
inferenceSlot (MVar _ slot _) = slot
inferenceSlot (MLit lit _) = Known (literalType lit)
inferenceSlot (MCall _ _ slot _) = slot
inferenceSlot (MTypeApp _ _ slot _) = slot
inferenceSlot (MLet _ _ _ slot _) = slot
inferenceSlot (MIf _ _ _ slot _) = slot
inferenceSlot (MLambda _ _ slot _) = slot
inferenceSlot (MClosure _ _ slot _) = slot
inferenceSlot (MConstruct _ _ _ slot _) = slot
inferenceSlot (MArrayLit _ slot _) = slot
inferenceSlot (MTuple _ slot _) = slot
inferenceSlot (MCase _ _ _ slot _) = slot
inferenceSlot (MFieldAccess _ _ slot _) = slot
inferenceSlot (MPanic _ slot _) = slot
