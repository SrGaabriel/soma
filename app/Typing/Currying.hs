module Typing.Currying where

import Typing.Types (Type(TArrow))

curryParams :: [(String, Type)] -> Type -> Type
curryParams params returnType =
    foldr
        (\(_, paramType) acc -> TArrow paramType acc)
        returnType
        params

getParamTypes :: Type -> [Type]
getParamTypes (TArrow param ret) = param : getParamTypes ret
getParamTypes _ = []

uncurryFunction :: Type -> Type -> ([Type], Type)
uncurryFunction a t =
    case t of
        TArrow b c ->
            let (args, ret) = uncurryFunction b c
            in (a : args, ret)
        _ -> ([a], t)