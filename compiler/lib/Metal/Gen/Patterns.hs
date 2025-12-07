module Metal.Gen.Patterns (
    stripAs,
    isDefaultPattern,
    constructorArity,
    validateArity,
    validateNoDuplicateBinders,
    hasWildcardLike,
    extractArms,
    patternMatchArity,
) where

import qualified Data.Set as Set
import Metal.Lift (collectBinders)
import Syntax.Patterns (
    ParsedPattern,
    Pattern (..),
    ResolvedPattern,
 )
import Syntax.Tree (Expr (..))

stripAs :: ResolvedPattern -> ResolvedPattern
stripAs (PAs _ p _) = stripAs p
stripAs p = p

isDefaultPattern :: ResolvedPattern -> Bool
isDefaultPattern p = case stripAs p of
    PVar{} -> True
    PWildcard{} -> True
    _ -> False

hasWildcardLike :: ResolvedPattern -> Bool
hasWildcardLike p = case stripAs p of
    PWildcard{} -> True
    _ -> False

constructorArity :: ResolvedPattern -> Int
constructorArity p = case stripAs p of
    PLit _ _ -> 0
    PConstructor _ ps _ -> length ps
    PTuple ps _ -> length ps
    PArray ps _ -> length ps
    _ -> 0

validateArity :: [[ResolvedPattern]] -> Bool
validateArity [] = True
validateArity (r : rs) =
    let n = length r
    in all ((== n) . length) rs

validateNoDuplicateBinders :: [[ResolvedPattern]] -> Bool
validateNoDuplicateBinders = all rowOk
  where
    rowOk ps =
        let vs = concatMap collectBinders ps
            s = Set.fromList vs
        in Set.size s == length vs

extractArms :: [Expr] -> [([ParsedPattern], Expr)]
extractArms = map extractArm
  where
    extractArm :: Expr -> ([ParsedPattern], Expr)
    extractArm (ExprPatternMatchArm pats body _) = (pats, body)
    extractArm _ = error "Not a pattern match arm"

patternMatchArity :: Expr -> Int
patternMatchArity (ExprPatternMatch _ arms _) =
    case extractArms arms of
        [] -> error "No arms in pattern match"
        ((pats, _) : _) -> length pats
patternMatchArity (ExprDerivedPatternMatch arms) =
    case extractArms arms of
        [] -> error "No arms in derived pattern match"
        ((pats, _) : _) -> length pats
patternMatchArity _ = error "Not a pattern match expression"
