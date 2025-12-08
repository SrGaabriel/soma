module Inference.Assembler (
    inferModule,
    inferBinding,
    applySubstitution,
    MetalTypeEnv,
) where

import Data.List (nub)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Inference.Core (InstanceEnv, TypedBinding, TypedInstance)
import Inference.Errors (InferenceError (..))
import Inference.Gen
import Inference.Solving (checkMetalConstraintEntailment, solveMetalTypeConstraints)
import Inference.Substitution (Subst, Substitutable (apply))
import Lexing.Position (Span)
import Metal.Expr
import Metal.Lower (LowerResult (..), untypedToInference)
import Metal.Metadata (FunctionAttributes)
import Metal.Module (MetallicConstructor (..), MetallicTypeDef (..))
import Project.Name (Name (..), nameToString)
import Syntax.Patterns (Literal (..), Pattern (..), ResolvedPattern)
import qualified Syntax.Tree
import Typing.Types (Constraint (..), QualifiedType (..), TyVar (..), Type (..), extractArrayElemType, extractTupleTypes, extractTypeArgs, splitFunctionType)

type ConstructorEnv = Map.Map Name (Name, [Type])

buildConstructorEnv :: [MetallicTypeDef] -> ConstructorEnv
buildConstructorEnv = foldr addTypeDef Map.empty
  where
    addTypeDef :: MetallicTypeDef -> ConstructorEnv -> ConstructorEnv
    addTypeDef (MAlgebraicType typeName ctors) env =
        foldr (addCtor typeName) env ctors
    addTypeDef (MStructType typeName ctorName fields) env =
        Map.insert ctorName (typeName, fields) env
    addTypeDef (MRecordType typeName fields) env =
        Map.insert typeName (typeName, map snd fields) env

    addCtor :: Name -> MetallicConstructor -> ConstructorEnv -> ConstructorEnv
    addCtor typeName (MetallicConstructor ctorName _ fields) = Map.insert ctorName (typeName, fields)

inferModule ::
    String ->
    String ->
    MetalTypeEnv ->
    InstanceEnv ->
    LowerResult ->
    ([InferenceError], [TypedBinding], [TypedInstance])
inferModule packageName moduleName typeEnv instanceEnv lowerResult = do
    let bindings = lrBindings lowerResult
    let instances = lrInstances lowerResult
    let ctorEnv = buildConstructorEnv (lrTypes lowerResult)

    let convertedBindings = convertBindings 0 bindings
    let convertedInstances = convertInstances (length bindings * 100) instances

    let (bindingErrors, typedBindings) =
            unzip
                [ inferBinding packageName moduleName typeEnv instanceEnv ctorEnv name body paramTypes retType tyVars constraints attrs
                | (name, body, paramTypes, retType, tyVars, constraints, attrs) <- convertedBindings
                ]

    let (instanceErrors, typedInstances) =
            unzip
                [ inferInstanceMethods packageName moduleName typeEnv instanceEnv ctorEnv constraintType methods
                | (constraintType, methods) <- convertedInstances
                ]

    let allErrors = concat bindingErrors ++ concat instanceErrors
    (nub allErrors, typedBindings, typedInstances)
  where
    convertBindings ::
        Int ->
        [(Name, UntypedExpr, [Type], Type, [TyVar], [Constraint], FunctionAttributes)] ->
        [(Name, InferenceExpr, [Type], Type, [TyVar], [Constraint], FunctionAttributes)]
    convertBindings _ [] = []
    convertBindings counter ((name, body, paramTypes, retType, tyVars, constraints, attrs) : rest) =
        let (inferBody, newCounter) = untypedToInference counter body
        in (name, inferBody, paramTypes, retType, tyVars, constraints, attrs) : convertBindings newCounter rest

    convertInstances ::
        Int ->
        [(QualifiedType, [(Name, UntypedExpr, [Type], Type)])] ->
        [(QualifiedType, [(Name, InferenceExpr, [Type], Type)])]
    convertInstances _ [] = []
    convertInstances counter ((constraintType, methods) : rest) =
        let (convertedMethods, newCounter) = convertMethods counter methods
        in (constraintType, convertedMethods) : convertInstances newCounter rest

    convertMethods ::
        Int ->
        [(Name, UntypedExpr, [Type], Type)] ->
        ([(Name, InferenceExpr, [Type], Type)], Int)
    convertMethods counter [] = ([], counter)
    convertMethods counter ((name, body, paramTypes, retType) : rest) =
        let (inferBody, newCounter) = untypedToInference counter body
            (restConverted, finalCounter) = convertMethods newCounter rest
        in ((name, inferBody, paramTypes, retType) : restConverted, finalCounter)

inferBinding ::
    String ->
    String ->
    MetalTypeEnv ->
    InstanceEnv ->
    ConstructorEnv ->
    Name ->
    InferenceExpr ->
    [Type] ->
    Type ->
    [TyVar] ->
    [Constraint] ->
    FunctionAttributes ->
    ([InferenceError], TypedBinding)
inferBinding packageName moduleName typeEnv instanceEnv ctorEnv name body paramTypes retType tyVars constraints attrs =
    let
        ((_, constraintSet), _genState, genErrors) =
            runMetalGenM packageName moduleName typeEnv
                $ generateBindingConstraints name body paramTypes retType tyVars constraints

        solveResult = solveMetalTypeConstraints (mcsTypeConstraints constraintSet)
    in
        case solveResult of
            Left solveErrors ->
                let typedBody = applySubstitution ctorEnv Map.empty body
                in (genErrors ++ solveErrors, (name, typedBody, paramTypes, retType, tyVars, constraints, attrs))
            Right typeSubst ->
                let classConstraints' = mcsClassConstraints constraintSet
                    declaredConstraints' = mcsDeclaredConstraints constraintSet
                    entailmentResult = checkMetalConstraintEntailment instanceEnv declaredConstraints' classConstraints' typeSubst
                in case entailmentResult of
                    Left entailmentErrors ->
                        let typedBody = applySubstitution ctorEnv typeSubst body
                        in (genErrors ++ entailmentErrors, (name, typedBody, paramTypes, retType, tyVars, constraints, attrs))
                    Right () ->
                        let typedBody = applySubstitution ctorEnv typeSubst body
                            -- Apply substitution to param types and return type for consistency
                            typedParamTypes = map (apply typeSubst) paramTypes
                            typedRetType = apply typeSubst retType
                            unresolvedErrors = checkUnresolvedTypeVars typedBody
                        in (genErrors ++ unresolvedErrors, (name, typedBody, typedParamTypes, typedRetType, tyVars, constraints, attrs))

inferInstanceMethods ::
    String ->
    String ->
    MetalTypeEnv ->
    InstanceEnv ->
    ConstructorEnv ->
    QualifiedType ->
    [(Name, InferenceExpr, [Type], Type)] ->
    ([InferenceError], TypedInstance)
inferInstanceMethods packageName moduleName typeEnv instanceEnv ctorEnv constraintType methods =
    let results =
            [ inferInstanceMethod packageName moduleName typeEnv instanceEnv ctorEnv name body paramTypes retType
            | (name, body, paramTypes, retType) <- methods
            ]
        (errorLists, typedMethods) = unzip results
    in (concat errorLists, (constraintType, typedMethods))

inferInstanceMethod ::
    String ->
    String ->
    MetalTypeEnv ->
    InstanceEnv ->
    ConstructorEnv ->
    Name ->
    InferenceExpr ->
    [Type] ->
    Type ->
    ([InferenceError], (Name, TypedExpr, [Type], Type))
inferInstanceMethod packageName moduleName typeEnv instanceEnv ctorEnv name body paramTypes retType =
    let
        ((_, constraintSet), _genState, genErrors) =
            runMetalGenM packageName moduleName typeEnv
                $ generateInstanceConstraints name body paramTypes retType

        solveResult = solveMetalTypeConstraints (mcsTypeConstraints constraintSet)
    in
        case solveResult of
            Left solveErrors ->
                let typedBody = applySubstitution ctorEnv Map.empty body
                in (genErrors ++ solveErrors, (name, typedBody, paramTypes, retType))
            Right typeSubst ->
                let classConstraints' = mcsClassConstraints constraintSet
                    entailmentResult' = checkMetalConstraintEntailment instanceEnv [] classConstraints' typeSubst
                in case entailmentResult' of
                    Left entailmentErrors ->
                        let typedBody = applySubstitution ctorEnv typeSubst body
                        in (genErrors ++ entailmentErrors, (name, typedBody, paramTypes, retType))
                    Right () ->
                        let typedBody = applySubstitution ctorEnv typeSubst body
                            typedParamTypes = map (apply typeSubst) paramTypes
                            typedRetType = apply typeSubst retType
                        in (genErrors, (name, typedBody, typedParamTypes, typedRetType))

applySubstitution :: ConstructorEnv -> Subst -> InferenceExpr -> TypedExpr
applySubstitution ctorEnv subst = go
  where
    resolveSlot :: TypeSlot -> Type
    resolveSlot (Known t) = apply subst t
    resolveSlot (Hole tv) = case Map.lookup tv subst of
        Just t -> apply subst t
        Nothing -> TVar tv

    resolveType :: Type -> Type
    resolveType = apply subst

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
        let typedScruts = map go scruts
            scrutTypes = map getType typedScruts
            typedArms = map (goArm scrutTypes) arms
        in MCase typedScruts typedArms (fmap go mdef) (resolveSlot slot) span'
    go (MFieldAccess e idx slot span') = MFieldAccess (go e) idx (resolveSlot slot) span'
    go (MPanic msg slot span') = MPanic msg (resolveSlot slot) span'

    goArm :: [Type] -> InferenceArm -> TypedArm
    goArm scrutTypes (MCaseArm pats body) =
        let typedPats = zipWith (typePattern ctorEnv resolveType) scrutTypes pats
        in MCaseArm typedPats (go body)

typePattern :: ConstructorEnv -> (Type -> Type) -> Type -> ResolvedPattern -> TypedPattern
typePattern ctorEnv resolve scrutTy pat = case pat of
    PVar name pSpan ->
        TPVar name scrutTy pSpan
    PWildcard pSpan ->
        TPWildcard scrutTy pSpan
    PLit lit pSpan ->
        TPLit lit scrutTy pSpan
    PAs name inner pSpan ->
        TPAs name (typePattern ctorEnv resolve scrutTy inner) scrutTy pSpan
    PConstructor ctorName innerPats pSpan ->
        let innerTyped = typeConstructorPatterns ctorEnv resolve scrutTy ctorName innerPats
        in TPConstructor ctorName innerTyped scrutTy pSpan
    PTuple innerPats pSpan ->
        let elemTypes = extractTupleTypes scrutTy
            innerTyped = zipWith (typePattern ctorEnv resolve) elemTypes innerPats
        in TPTuple innerTyped scrutTy pSpan
    PArray innerPats pSpan ->
        let elemType = extractArrayElemType scrutTy
            innerTyped = map (typePattern ctorEnv resolve elemType) innerPats
        in TPArray innerTyped scrutTy pSpan

typeConstructorPatterns :: ConstructorEnv -> (Type -> Type) -> Type -> Name -> [ResolvedPattern] -> [TypedPattern]
typeConstructorPatterns ctorEnv resolve scrutTy ctorName innerPats =
    case Map.lookup ctorName ctorEnv of
        Just (_typeName, fieldTypes) ->
            let typeArgs = extractTypeArgs scrutTy
                instantiatedFieldTypes = map (instantiateFieldType resolve typeArgs) fieldTypes
            in zipWith (typePattern ctorEnv resolve) instantiatedFieldTypes innerPats
        Nothing ->
            map (typePattern ctorEnv resolve (extractFieldTypeFallback scrutTy)) innerPats
  where
    instantiateFieldType :: (Type -> Type) -> [Type] -> Type -> Type
    instantiateFieldType resolveT typeArgs fieldTy = case fieldTy of
        TVar _ ->
            case typeArgs of
                (arg : _) -> resolveT arg
                [] -> resolveT fieldTy
        TApp f a ->
            TApp (instantiateFieldType resolveT typeArgs f) (instantiateFieldType resolveT typeArgs a)
        TArrow a b ->
            TArrow (instantiateFieldType resolveT typeArgs a) (instantiateFieldType resolveT typeArgs b)
        _ -> resolveT fieldTy

    extractFieldTypeFallback :: Type -> Type
    extractFieldTypeFallback (TApp _ arg) = resolve arg
    extractFieldTypeFallback t = resolve t

checkUnresolvedTypeVars :: TypedExpr -> [InferenceError]
checkUnresolvedTypeVars expr = nub $ go expr
  where
    go :: TypedExpr -> [InferenceError]
    go (MVar _ ty span') = checkType span' ty
    go (MLit _ _) = []
    go (MCall callee args ty span') = go callee ++ concatMap go args ++ checkType span' ty
    go (MTypeApp e _ ty span') = go e ++ checkType span' ty
    go (MLet _ val body ty span') = go val ++ go body ++ checkType span' ty
    go (MLambda params body ty span') = concatMap (checkType span' . snd) params ++ go body ++ checkType span' ty
    go (MClosure _ captures ty span') = concatMap (checkType span' . snd) captures ++ checkType span' ty
    go (MConstruct _ _ args ty span') = concatMap go args ++ checkType span' ty
    go (MArrayLit elems ty span') = concatMap go elems ++ checkType span' ty
    go (MTuple elems ty span') = concatMap go elems ++ checkType span' ty
    go (MIf cond thenE elseE ty span') = go cond ++ go thenE ++ go elseE ++ checkType span' ty
    go (MCase scruts arms mdef ty span') =
        concatMap go scruts ++ concatMap goArm arms ++ maybe [] go mdef ++ checkType span' ty
    go (MFieldAccess e _ ty span') = go e ++ checkType span' ty
    go (MPanic _ ty span') = checkType span' ty

    goArm :: TypedArm -> [InferenceError]
    goArm (MCaseArm _ body) = go body

    checkType :: Span -> Type -> [InferenceError]
    checkType span' ty =
        let vars = collectTypeVars ty
        in [UnresolvedTypeVariable (dummyExpr span') (tvId v) ty | v <- Set.toList vars]

    collectTypeVars :: Type -> Set.Set TyVar
    collectTypeVars (TVar tv) = Set.singleton tv
    collectTypeVars (TApp a b) = collectTypeVars a `Set.union` collectTypeVars b
    collectTypeVars (TArrow a b) = collectTypeVars a `Set.union` collectTypeVars b
    collectTypeVars _ = Set.empty

    -- todo(magic-spans): remove workaround
    dummyExpr :: Span -> Syntax.Tree.Expr
    dummyExpr = Syntax.Tree.ExprNum "0"
