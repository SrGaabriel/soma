module Metal.Gen.Patterns (
    stripAs,
    isDefaultPattern,
    constructorArity,
    collectBinders,
    validateArity,
    validateNoDuplicateBinders,
    hasWildcardLike,
) where

import qualified Data.Set as Set
import Syntax.Patterns (
    Pattern (..),
 )

stripAs :: Pattern -> Pattern
stripAs (PAs _ p) = stripAs p
stripAs p = p

isDefaultPattern :: Pattern -> Bool
isDefaultPattern p = case stripAs p of
    PVar{} -> True
    PWildcard -> True
    _ -> False

hasWildcardLike :: Pattern -> Bool
hasWildcardLike p = case stripAs p of
    PWildcard -> True
    _ -> False

constructorArity :: Pattern -> Int
constructorArity p = case stripAs p of
    PLit _ -> 0
    PConstructor _ ps -> length ps
    PTuple ps -> length ps
    PArray ps -> length ps
    _ -> 0

collectBinders :: Pattern -> [String]
collectBinders (PVar v) = [v]
collectBinders (PAs v p) = v : collectBinders p
collectBinders (PConstructor _ ps) = concatMap collectBinders ps
collectBinders (PTuple ps) = concatMap collectBinders ps
collectBinders (PArray ps) = concatMap collectBinders ps
collectBinders _ = []

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
