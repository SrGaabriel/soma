module Project.Name where

type Name = String

data EventualName = Name
    { nModule :: String
    , nBase :: String
    }
    deriving (Show, Eq, Ord)
