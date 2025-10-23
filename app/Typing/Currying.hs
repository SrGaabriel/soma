module Typing.Currying where

import Typing.Types (Kind (KindArrow), QualifiedType (Forall), Type (..), assignConstraints)

curryParams :: [(String, Type)] -> Type -> Type
curryParams params returnType =
    foldr
        (\(_, paramType) acc -> TArrow paramType acc)
        returnType
        params

getParamTypes :: Type -> [Type]
getParamTypes (TArrow param ret) = param : getParamTypes ret
getParamTypes _ = []

curryFunction :: [Type] -> Type -> Type
curryFunction rest returnType = foldr TArrow returnType rest

uncurryFunction :: Type -> ([Type], Type)
uncurryFunction (TArrow a b) =
    let (args, ret) = uncurryFunction b
    in (a : args, ret)
uncurryFunction t = ([], t)

uncurryKind :: Kind -> ([Kind], Kind)
uncurryKind (KindArrow k1 k2) =
    let (args, ret) = uncurryKind k2
    in (k1 : args, ret)
uncurryKind k = ([], k)

uncurryQualified :: QualifiedType -> ([QualifiedType], QualifiedType)
uncurryQualified qual@(Forall _ _ t@(TArrow _ _)) =
    let (args, ret) = uncurryFunction t
        constrainedArgs = map (assignConstraints qual) args
        constrainedRet = assignConstraints qual ret
    in (constrainedArgs, constrainedRet)
uncurryQualified qual = ([], qual)

uncurryTypeApp :: Type -> (Type, [Type])
uncurryTypeApp t = go t []
  where
    go (TApp f arg) args = go f (arg : args)
    go func args = (func, args)