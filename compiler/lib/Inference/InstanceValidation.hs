module Inference.InstanceValidation where

import qualified Data.Map as Map
import Inference.Core (InstanceEnv)
import Inference.Errors (InferenceError (..))
import Inference.Substitution (Substitutable (apply))
import Lexing.Position (Located (..))
import Syntax.Tree (Expr (..), exprChildren)
import Typing.Types (Constraint (..), QualifiedType (..), TyConstructor (..), TyVar (..), Type (..), constraintType, tyUniqueName)

validateInstances :: InstanceEnv -> Expr -> [InferenceError]
validateInstances instEnv expr =
    let typeClassDefs = collectTypeClassDefs expr
        instanceDefs = collectInstances expr
    in concatMap (validateInstance typeClassDefs instEnv) instanceDefs

collectTypeClassDefs :: Expr -> Map.Map String QualifiedType
collectTypeClassDefs expr = Map.fromList (go expr)
  where
    go (ExprTypeClassDef name (Located _ ty) _ _) = [(name, ty)]
    go (ExprRoot children) = concatMap go children
    go e = concatMap go (exprChildren e)

validateInstance :: Map.Map String QualifiedType -> InstanceEnv -> Expr -> [InferenceError]
validateInstance typeClassDefs instEnv expr@(ExprInstanceDef instanceQualType _ _) =
    let Forall _ instanceConstraints instanceType = instanceQualType
    in case getTypeClassName instanceType of
        Nothing -> []
        Just className ->
            case Map.lookup className typeClassDefs of
                Nothing -> []
                Just (Forall tvs superclassConstraints _) ->
                    validateSuperclasses expr instanceQualType tvs superclassConstraints instanceConstraints instEnv
validateInstance _ _ _ = []

collectInstances :: Expr -> [Expr]
collectInstances e@(ExprInstanceDef{}) = [e]
collectInstances (ExprRoot children) = concatMap collectInstances children
collectInstances e = concatMap collectInstances (exprChildren e)

getTypeClassName :: Type -> Maybe String
getTypeClassName (TConstructor (TypeConstructor tyId _)) = Just (tyUniqueName tyId)
getTypeClassName (TApp f _) = getTypeClassName f
getTypeClassName _ = Nothing

getInstanceType :: Type -> Type
getInstanceType (TApp _ arg) = arg
getInstanceType t = t

validateSuperclasses ::
    Expr ->
    QualifiedType ->
    [TyVar] ->
    [Constraint] ->
    [Constraint] ->
    InstanceEnv ->
    [InferenceError]
validateSuperclasses instanceExpr instanceQualType tvs superclassConstraints instanceConstraints instEnv =
    let Forall _ _ instanceConstraintType = instanceQualType
        instanceType = getInstanceType instanceConstraintType
        subst = buildSubstitution tvs instanceType
        requiredConstraints = apply subst superclassConstraints
        requiredTypes = map constraintType requiredConstraints
        declaredConstraintTypes = map constraintType instanceConstraints
        unsatisfied = [Constraint ty | ty <- requiredTypes, not (Map.member instanceQualType instEnv) && ty `notElem` declaredConstraintTypes]
    in map (MissingSuperclassInstance instanceExpr instanceType) unsatisfied

buildSubstitution :: [TyVar] -> Type -> Map.Map TyVar Type
buildSubstitution tvs instanceType =
    case (tvs, instanceType) of
        ([tv], _) ->
            Map.singleton tv instanceType
        (_, TApp _ _) ->
            let typeArgs = extractTypeArgs instanceType
            in if length tvs == length typeArgs
                then Map.fromList (zip tvs typeArgs)
                else Map.fromList [(tv, instanceType) | tv <- tvs]
        _ ->
            Map.fromList [(tv, instanceType) | tv <- tvs]
  where
    extractTypeArgs :: Type -> [Type]
    extractTypeArgs (TApp f arg) = extractTypeArgs f ++ [arg]
    extractTypeArgs _ = []
