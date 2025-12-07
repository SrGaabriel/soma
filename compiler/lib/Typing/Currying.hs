module Typing.Currying (curryFunction, uncurryKind) where

import Typing.Types (Kind (KindArrow), Type (..))

curryFunction :: [Type] -> Type -> Type
curryFunction rest returnType = foldr TArrow returnType rest

uncurryKind :: Kind -> ([Kind], Kind)
uncurryKind (KindArrow k1 k2) =
    let (args, ret) = uncurryKind k2
    in (k1 : args, ret)
uncurryKind k = ([], k)
