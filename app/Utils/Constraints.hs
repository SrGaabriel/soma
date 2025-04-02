module Utils.Constraints where

import qualified Data.Map as Map
import Parsing.Type (GenericConstraint (GenericConstraint), Type (..), StructConstructor (constructorFields))

batchApplyClassConstraint :: GenericConstraint -> [Type] -> [Type]
batchApplyClassConstraint contraint types = map (applyClassConstraint contraint) types

applyClassConstraint :: GenericConstraint -> Type -> Type
applyClassConstraint (GenericConstraint generic classs) (GenericType generic2 constraints)
    | generic == generic2 = GenericType generic (classs : constraints)
    | otherwise = GenericType generic constraints
applyClassConstraint constraint (FunctionType arg ret) =
    FunctionType (applyClassConstraint constraint arg) (applyClassConstraint constraint ret)
applyClassConstraint constraint (StructType name variants mgs) =
    StructType name (map (\v -> v{constructorFields = Map.map (applyClassConstraint constraint) (constructorFields v)}) variants) (fmap (map (applyClassConstraint constraint)) mgs)
applyClassConstraint _ t = t
