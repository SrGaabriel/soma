module Typing.Currying where

import Typing.Types (Kind (KindArrow), Type (TArrow))

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
curryFunction [] returnType = returnType
curryFunction (paramType : rest) returnType =
    TArrow paramType (curryFunction rest returnType)

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