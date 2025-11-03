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
isDefaultPattern PVar{} = True
isDefaultPattern PWildcard = True
isDefaultPattern (PAs _ _) = True
isDefaultPattern _ = False

hasWildcardLike :: Pattern -> Bool
hasWildcardLike PWildcard = True
hasWildcardLike (PAs _ p) = hasWildcardLike p
hasWildcardLike _ = False

constructorArity :: Pattern -> Int
constructorArity (PLit _) = 0
constructorArity (PConstructor _ ps) = length ps
constructorArity (PTuple ps) = length ps
constructorArity (PArray ps) = length ps
constructorArity (PAs _ p) = constructorArity p
constructorArity _ = 0

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
        in noDups vs
    noDups xs =
        let s = Set.fromList xs
        in Set.size s == length xs

-- todo: maranget-style pat
