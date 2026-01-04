module Ide.Query.Durability (
    Durability (..),
    Revision,
    initialRevision,
    nextRevision,
) where

import Data.Word (Word64)

data Durability
    = Low
    | Medium
    | High
    deriving (Eq, Ord, Show, Enum, Bounded)

newtype Revision = Revision {unRevision :: Word64}
    deriving (Eq, Ord, Show)

initialRevision :: Revision
initialRevision = Revision 0

nextRevision :: Revision -> Revision
nextRevision (Revision r) = Revision (r + 1)
