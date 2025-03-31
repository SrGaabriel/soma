module Utils.Currying (curryParams, uncurryFunction) where

import qualified Data.Map as Map
import Parsing.Type (Type (..))

curryParams :: Map.Map String Type -> Type -> Type
curryParams params returnType =
    Prelude.foldr
        (\paramType acc -> FunctionType paramType acc)
        returnType
        (Map.elems params)

uncurryFunction :: Type -> Type -> ([Type], Type)
uncurryFunction a t =
    case t of
        FunctionType b c ->
            let (args, ret) = uncurryFunction b c
            in (a : args, ret)
        _ -> ([a], t)
