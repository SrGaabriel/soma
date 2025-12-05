{-# LANGUAGE FlexibleInstances #-}

module Inference.Solving (
    solveMetalTypeConstraints,
    checkMetalConstraintEntailment,
    unifyTypes,
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Inference.Core (InstanceEnv, UnificationPurpose (..))
import Inference.Errors (InferenceError (..))
import Inference.Gen (MetalClassConstraint (..), MetalTypeConstraint (..))
import Inference.Substitution (Subst, Substitutable (apply, ftv), composeSubst)
import Lexing.Position (Span (..))
import qualified Syntax.Tree
import Typing.Types (Constraint (..), Kind (..), QualifiedType (..), TyConstructor (..), TyVar (..), Type (..), constraintType)

solveMetalTypeConstraints :: [MetalTypeConstraint] -> Either [InferenceError] Subst
solveMetalTypeConstraints = foldMWithErrors solveOne Map.empty
  where
    solveOne :: Subst -> MetalTypeConstraint -> Either [InferenceError] Subst
    solveOne currentSubst (MetalTypeConstraint span' expected actual purpose) = do
        let expected' = apply currentSubst expected
        let actual' = apply currentSubst actual
        newSubst <- unifyTypes span' purpose expected' actual'
        pure (composeSubst newSubst currentSubst)

unifyTypes :: Span -> UnificationPurpose -> Type -> Type -> Either [InferenceError] Subst
unifyTypes _ _ t1 t2 | t1 == t2 = Right Map.empty
unifyTypes span' _ (TVar tv) t = bindVar span' tv t
unifyTypes span' _ t (TVar tv) = bindVar span' tv t
unifyTypes span' p (TArrow l1 r1) (TArrow l2 r2) = do
    s1 <- unifyTypes span' p l1 l2
    s2 <- unifyTypes span' p (apply s1 r1) (apply s1 r2)
    pure (composeSubst s2 s1)
unifyTypes span' p (TApp f1 a1) (TApp f2 a2) = do
    s1 <- unifyTypes span' p f1 f2
    s2 <- unifyTypes span' p (apply s1 a1) (apply s1 a2)
    pure (composeSubst s2 s1)
unifyTypes span' p t1 t2 = Left [generateErrorForPurpose p span' t1 t2]

bindVar :: Span -> TyVar -> Type -> Either [InferenceError] Subst
bindVar span' tv t
    | t == TVar tv = Right Map.empty
    | tv `Set.member` ftv t = Left [CircularTypeDependency (dummyExpr span')]
    | otherwise = Right $ Map.singleton tv t

checkMetalConstraintEntailment ::
    InstanceEnv ->
    [Constraint] ->
    [MetalClassConstraint] ->
    Subst ->
    Either [InferenceError] ()
checkMetalConstraintEntailment instanceEnv declaredConstraints classConstraints typeSubst = do
    let inferredConstraints =
            [ (apply typeSubst (mccConstraint cc), mccSpan cc)
            | cc <- classConstraints
            ]
    let unsatisfiedConstraints = filter (not . isConstraintSatisfied) inferredConstraints
    case unsatisfiedConstraints of
        [] -> Right ()
        _ -> Left [MissingClassConstraint (dummyExpr span') constraint | (constraint, span') <- unsatisfiedConstraints]
  where
    isConstraintSatisfied (constraint, _) =
        isEntailedByInstanceEnv instanceEnv constraint || isEntailedBy declaredConstraints constraint

isEntailedByInstanceEnv :: InstanceEnv -> Constraint -> Bool
isEntailedByInstanceEnv instanceEnv constraint =
    let constraintTy = constraintType constraint
        instances = Map.toList instanceEnv
        matches = filter (\(Forall _ _ instanceTy, _) -> canUnify instanceTy constraintTy) instances
    in not (null matches)
  where
    canUnify ty1 ty2 =
        let ty1' = eraseKinds ty1
            ty2' = eraseKinds ty2
        in case unifyTypes dummySpan UnifyFunctionApplication ty1' ty2' of
            Right _ -> True
            Left _ -> False

    eraseKinds (TConstructor (TypeConstructor name _)) = TConstructor (TypeConstructor name KindStar)
    eraseKinds (TVar tv) = TVar tv
    eraseKinds (TApp f a) = TApp (eraseKinds f) (eraseKinds a)
    eraseKinds (TArrow a b) = TArrow (eraseKinds a) (eraseKinds b)
    eraseKinds t = t

isEntailedBy :: [Constraint] -> Constraint -> Bool
isEntailedBy declaredCs constraint =
    let constraintTy = constraintType constraint
    in any (\declaredC -> constraintType declaredC == constraintTy) declaredCs

generateErrorForPurpose :: UnificationPurpose -> Span -> Type -> Type -> InferenceError
generateErrorForPurpose UnifyFunctionBody span' expected actual =
    FunctionBodyTypeMismatch (dummyExpr span') expected actual
generateErrorForPurpose UnifyFunctionApplication span' expected actual =
    FunctionApplicationTypeMismatch (dummyExpr span') expected actual
generateErrorForPurpose UnifyPatternMatchArmBody span' expected actual =
    PatternMatchArmTypeMismatch (dummyExpr span') expected actual
generateErrorForPurpose UnifyPatternMatchArms span' expected actual =
    PatternMatchArmsTypeMismatch (dummyExpr span') expected actual
generateErrorForPurpose UnifyPatternConstructor span' expected actual =
    PatternConstructorTypeMismatch (dummyExpr span') expected actual
generateErrorForPurpose UnifyIfCondition span' _ actual =
    IfConditionShouldBeBool (dummyExpr span') actual
generateErrorForPurpose UnifyIfElseBranches span' thenType elseType =
    IfElseBranchTypeMismatch (dummyExpr span') thenType elseType

foldMWithErrors :: (b -> a -> Either [e] b) -> b -> [a] -> Either [e] b
foldMWithErrors _ acc [] = Right acc
foldMWithErrors f acc (x : xs) = case f acc x of
    Left errs -> case foldMWithErrors f acc xs of
        Left moreErrs -> Left (errs ++ moreErrs)
        Right _ -> Left errs
    Right acc' -> foldMWithErrors f acc' xs

    -- todo(magic-spans): remove workaround
dummyExpr :: Span -> Syntax.Tree.Expr
dummyExpr = Syntax.Tree.ExprNum "0"

-- todo(magic-spans): remove workaround
dummySpan :: Span
dummySpan = Span 0 0
