module Utils.Constraints where

import Parsing.Type (GenericConstraint (GenericConstraint), Type (..), mapType)

batchApplyClassConstraint :: GenericConstraint -> [Type] -> [Type]
batchApplyClassConstraint contraint types = map (applyClassConstraint contraint) types

applyClassConstraint :: GenericConstraint -> Type -> Type
applyClassConstraint (GenericConstraint generic classs) = mapType f
  where
    f (GenericType generic2 constraints)
        | generic == generic2 = GenericType generic2 (classs : constraints)
        | otherwise = GenericType generic2 constraints
    f t = t