module Utils.Currying (curryParams, uncurryFunction, getParamTypes) where

import Parsing.Type (Type (..))

curryParams :: [(String, Type)] -> Type -> Type
curryParams params returnType =
    foldr
        (\(_, paramType) acc -> FunctionType paramType acc)
        returnType
        params

getParamTypes :: Type -> [Type]
getParamTypes (FunctionType param ret) = param : getParamTypes ret
getParamTypes _ = []

uncurryFunction :: Type -> Type -> ([Type], Type)
uncurryFunction a t =
    case t of
        FunctionType b c ->
            let (args, ret) = uncurryFunction b c
            in (a : args, ret)
        _ -> ([a], t)
