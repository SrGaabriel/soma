module Inference.Assembler (
    inferModule,
    inferBinding,
    applySubstitution,
    MetalTypeEnv,
) where

import Data.List (nub)
import qualified Data.Map as Map
import Inference.Core (InstanceEnv)
import Inference.Errors (InferenceError (..))
import Inference.Gen
import Inference.Solving (checkMetalConstraintEntailment, solveMetalTypeConstraints)
import Inference.Substitution (Subst, Substitutable (apply))
import Metal.Expr
import Metal.Lower (LowerResult (..))
import Typing.Types (Constraint (..), QualifiedType (..), TyVar (..), Type (..))

inferModule ::
    String ->
    String ->
    MetalTypeEnv ->
    InstanceEnv ->
    LowerResult ->
    ([InferenceError], [(String, TypedExpr, [Type], Type, [TyVar], [Constraint], Bool)])
inferModule packageName moduleName typeEnv instanceEnv lowerResult = do
    let bindings = lrBindings lowerResult
    let instances = lrInstances lowerResult

    let (bindingErrors, typedBindings) =
            unzip
                [ inferBinding packageName moduleName typeEnv instanceEnv name body paramTypes retType tyVars constraints isInline
                | (name, body, paramTypes, retType, tyVars, constraints, isInline) <- bindings
                ]

    let (instanceErrors, _typedInstances) =
            unzip
                [ inferInstanceMethods packageName moduleName typeEnv instanceEnv constraintType methods
                | (constraintType, methods) <- instances
                ]

    let allErrors = concat bindingErrors ++ concat instanceErrors
    (nub allErrors, typedBindings)

inferBinding ::
    String ->
    String ->
    MetalTypeEnv ->
    InstanceEnv ->
    String ->
    InferenceExpr ->
    [Type] ->
    Type ->
    [TyVar] ->
    [Constraint] ->
    Bool ->
    ([InferenceError], (String, TypedExpr, [Type], Type, [TyVar], [Constraint], Bool))
inferBinding packageName moduleName typeEnv instanceEnv name body paramTypes retType tyVars constraints isInline =
    let
        ((_, constraintSet), _genState, genErrors) =
            runMetalGenM packageName moduleName typeEnv
                $ generateBindingConstraints name body paramTypes retType tyVars constraints

        solveResult = solveMetalTypeConstraints (mcsTypeConstraints constraintSet)
    in
        case solveResult of
            Left solveErrors ->
                let typedBody = applySubstitution Map.empty body
                in (genErrors ++ solveErrors, (name, typedBody, paramTypes, retType, tyVars, constraints, isInline))
            Right typeSubst ->
                let classConstraints' = mcsClassConstraints constraintSet
                    declaredConstraints' = mcsDeclaredConstraints constraintSet
                    entailmentResult = checkMetalConstraintEntailment instanceEnv declaredConstraints' classConstraints' typeSubst
                in case entailmentResult of
                    Left entailmentErrors ->
                        let typedBody = applySubstitution typeSubst body
                        in (genErrors ++ entailmentErrors, (name, typedBody, paramTypes, retType, tyVars, constraints, isInline))
                    Right () ->
                        let typedBody = applySubstitution typeSubst body
                            -- Apply substitution to param types and return type for consistency
                            typedParamTypes = map (apply typeSubst) paramTypes
                            typedRetType = apply typeSubst retType
                        in (genErrors, (name, typedBody, typedParamTypes, typedRetType, tyVars, constraints, isInline))

inferInstanceMethods ::
    String ->
    String ->
    MetalTypeEnv ->
    InstanceEnv ->
    QualifiedType ->
    [(String, InferenceExpr, [Type], Type)] ->
    ([InferenceError], [(String, TypedExpr, [Type], Type)])
inferInstanceMethods packageName moduleName typeEnv instanceEnv _constraintType methods =
    let results =
            [ inferInstanceMethod packageName moduleName typeEnv instanceEnv name body paramTypes retType
            | (name, body, paramTypes, retType) <- methods
            ]
        (errorLists, typedMethods) = unzip results
    in (concat errorLists, typedMethods)

inferInstanceMethod ::
    String ->
    String ->
    MetalTypeEnv ->
    InstanceEnv ->
    String ->
    InferenceExpr ->
    [Type] ->
    Type ->
    ([InferenceError], (String, TypedExpr, [Type], Type))
inferInstanceMethod packageName moduleName typeEnv instanceEnv name body paramTypes retType =
    let
        ((_, constraintSet), _genState, genErrors) =
            runMetalGenM packageName moduleName typeEnv
                $ generateInstanceConstraints name body paramTypes retType

        solveResult = solveMetalTypeConstraints (mcsTypeConstraints constraintSet)
    in
        case solveResult of
            Left solveErrors ->
                let typedBody = applySubstitution Map.empty body
                in (genErrors ++ solveErrors, (name, typedBody, paramTypes, retType))
            Right typeSubst ->
                let classConstraints' = mcsClassConstraints constraintSet
                    entailmentResult' = checkMetalConstraintEntailment instanceEnv [] classConstraints' typeSubst
                in case entailmentResult' of
                    Left entailmentErrors ->
                        let typedBody = applySubstitution typeSubst body
                        in (genErrors ++ entailmentErrors, (name, typedBody, paramTypes, retType))
                    Right () ->
                        let typedBody = applySubstitution typeSubst body
                            typedParamTypes = map (apply typeSubst) paramTypes
                            typedRetType = apply typeSubst retType
                        in (genErrors, (name, typedBody, typedParamTypes, typedRetType))

applySubstitution :: Subst -> InferenceExpr -> TypedExpr
applySubstitution subst = go
  where
    resolveSlot :: TypeSlot -> Type
    resolveSlot (Known t) = apply subst t
    resolveSlot (Hole tv) = case Map.lookup tv subst of
        Just t -> apply subst t
        Nothing -> TVar tv

    go :: InferenceExpr -> TypedExpr
    go (MVar name slot span') = MVar name (resolveSlot slot) span'
    go (MLit lit span') = MLit lit span'
    go (MCall callee args slot span') = MCall (go callee) (map go args) (resolveSlot slot) span'
    go (MTypeApp e tys slot span') = MTypeApp (go e) tys (resolveSlot slot) span'
    go (MLet name val body slot span') = MLet name (go val) (go body) (resolveSlot slot) span'
    go (MLambda params body slot span') =
        let typedParams = [(n, resolveSlot s) | (n, s) <- params]
        in MLambda typedParams (go body) (resolveSlot slot) span'
    go (MClosure name captures slot span') =
        let typedCaptures = [(n, resolveSlot s) | (n, s) <- captures]
        in MClosure name typedCaptures (resolveSlot slot) span'
    go (MConstruct name tag args slot span') = MConstruct name tag (map go args) (resolveSlot slot) span'
    go (MArrayLit elems slot span') = MArrayLit (map go elems) (resolveSlot slot) span'
    go (MTuple elems slot span') = MTuple (map go elems) (resolveSlot slot) span'
    go (MIf cond thenE elseE slot span') = MIf (go cond) (go thenE) (go elseE) (resolveSlot slot) span'
    go (MCase scruts arms mdef slot span') =
        MCase (map go scruts) (map goArm arms) (fmap go mdef) (resolveSlot slot) span'
    go (MFieldAccess e idx slot span') = MFieldAccess (go e) idx (resolveSlot slot) span'
    go (MPanic msg slot span') = MPanic msg (resolveSlot slot) span'

    goArm :: InferenceArm -> TypedArm
    goArm (MCaseArm pats body) = MCaseArm pats (go body)
