{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Soma.Unique where

import Data.Coerce (coerce)
import Data.IntMap.Strict qualified as IM
import Prelude hiding (lookup)

newtype Unique = Unique Int deriving (Show, Eq, Ord)

newtype UniqueMap a = UniqueMap (IM.IntMap a)
    deriving newtype (Show, Eq, Ord, Semigroup, Monoid, Functor, Foldable)
    deriving stock (Traversable)

empty :: forall a. UniqueMap a
empty = coerce (IM.empty @a)

singleton :: forall a. Unique -> a -> UniqueMap a
singleton = coerce (IM.singleton @a)

insert :: forall a. Unique -> a -> UniqueMap a -> UniqueMap a
insert = coerce (IM.insert @a)

insertWith :: forall a. (a -> a -> a) -> Unique -> a -> UniqueMap a -> UniqueMap a
insertWith = coerce (IM.insertWith @a)

lookup :: forall a. Unique -> UniqueMap a -> Maybe a
lookup = coerce (IM.lookup @a)

member :: forall a. Unique -> UniqueMap a -> Bool
member = coerce (IM.member @a)

delete :: forall a. Unique -> UniqueMap a -> UniqueMap a
delete = coerce (IM.delete @a)

adjust :: forall a. (a -> a) -> Unique -> UniqueMap a -> UniqueMap a
adjust = coerce (IM.adjust @a)

alter :: forall a. (Maybe a -> Maybe a) -> Unique -> UniqueMap a -> UniqueMap a
alter = coerce (IM.alter @a)

fromList :: forall a. [(Unique, a)] -> UniqueMap a
fromList = coerce (IM.fromList @a)

toList :: forall a. UniqueMap a -> [(Unique, a)]
toList = coerce (IM.toList @a)

keys :: forall a. UniqueMap a -> [Unique]
keys = coerce (IM.keys @a)

elems :: forall a. UniqueMap a -> [a]
elems = coerce (IM.elems @a)
