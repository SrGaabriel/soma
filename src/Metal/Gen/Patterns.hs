module Metal.Gen.Patterns (
    stripAs,
    isDefaultPattern,
    constructorArity,
    validateArity,
    validateNoDuplicateBinders,
    hasWildcardLike,
) where

import qualified Data.Set as Set
import Syntax.Patterns (
    Pattern (..),
 )
import Metal.Lift (collectBinders)

stripAs :: Pattern -> Pattern
stripAs (PAs _ p _) = stripAs p
stripAs p = p

isDefaultPattern :: Pattern -> Bool
isDefaultPattern p = case stripAs p of
    PVar{} -> True
    PWildcard{} -> True
    _ -> False

hasWildcardLike :: Pattern -> Bool
hasWildcardLike p = case stripAs p of
    PWildcard{} -> True
    _ -> False

constructorArity :: Pattern -> Int
constructorArity p = case stripAs p of
    PLit _ _ -> 0
    PConstructor _ ps _ -> length ps
    PTuple ps _ -> length ps
    PArray ps _ -> length ps
    _ -> 0

validateArity :: [[Pattern]] -> Bool
validateArity [] = True
validateArity (r : rs) =
    let n = length r
    in all ((== n) . length) rs

validateNoDuplicateBinders :: [[Pattern]] -> Bool
validateNoDuplicateBinders = all rowOk
  where
    rowOk ps =
        let vs = concatMap collectBinders ps
            s = Set.fromList vs
        in Set.size s == length vs
