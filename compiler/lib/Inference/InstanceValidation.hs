module Inference.InstanceValidation where

import qualified Data.Map as Map
import Inference.Core (InstanceEnv)
import Inference.Errors (InferenceError (..))
import Inference.Substitution (Substitutable (apply))
import Lexing.Position (Located (..))
import Syntax.Tree (Expr (..), exprChildren)
import Typing.Types (Constraint (..), QualifiedType (..), TyConstructor (..), TyVar (..), Type (..), constraintType)

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
validateInstance typeClassDefs instEnv expr@(ExprInstanceDef instanceConstraintType _ _) =
    case getTypeClassName instanceConstraintType of
        Nothing -> []
        Just className ->
            case Map.lookup className typeClassDefs of
                Nothing -> []
                Just (Forall tvs superclassConstraints _) ->
                    validateSuperclasses expr instanceConstraintType tvs superclassConstraints instEnv
validateInstance _ _ _ = []

collectInstances :: Expr -> [Expr]
collectInstances e@(ExprInstanceDef{}) = [e]
collectInstances (ExprRoot children) = concatMap collectInstances children
collectInstances e = concatMap collectInstances (exprChildren e)

getTypeClassName :: Type -> Maybe String
getTypeClassName (TConstructor (TypeConstructor name _)) = Just name
getTypeClassName (TApp f _) = getTypeClassName f
getTypeClassName _ = Nothing

getInstanceType :: Type -> Type
getInstanceType (TApp _ arg) = arg
getInstanceType t = t

validateSuperclasses ::
    Expr ->
    Type ->
    [TyVar] ->
    [Constraint] ->
    InstanceEnv ->
    [InferenceError]
validateSuperclasses instanceExpr instanceConstraintType tvs superclassConstraints instEnv =
    let instanceType = getInstanceType instanceConstraintType
        subst = buildSubstitution tvs instanceType
        requiredConstraints = apply subst superclassConstraints
        requiredTypes = map constraintType requiredConstraints
        unsatisfied = [Constraint ty | ty <- requiredTypes, not (Map.member ty instEnv)]
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
