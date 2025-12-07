{-# LANGUAGE DeriveGeneric #-}

module Project.Unique (
    Unique (..),
    UniqueId,

    UniqueSupply,
    UniqueSupplyState (..),
    runUniqueSupply,
    evalUniqueSupply,
    execUniqueSupply,

    freshUnique,
    freshUniqueFrom,

    initialSupplyState,
) where

import Control.Monad.State.Strict (State, evalState, execState, get, put, runState)
import Data.Hashable (Hashable (..))
import GHC.Generics (Generic)

type UniqueId = Int

data Unique = Unique
    { uniqueId :: !UniqueId
    , uniqueModule :: !String
    , uniqueOriginal :: !String
    }
    deriving (Show, Generic)

instance Eq Unique where
    u1 == u2 = uniqueId u1 == uniqueId u2 && uniqueModule u1 == uniqueModule u2

instance Ord Unique where
    compare u1 u2 =
        case compare (uniqueModule u1) (uniqueModule u2) of
            EQ -> compare (uniqueId u1) (uniqueId u2)
            other -> other

instance Hashable Unique where
    hashWithSalt salt u =
        salt `hashWithSalt` uniqueId u `hashWithSalt` uniqueModule u

data UniqueSupplyState = UniqueSupplyState
    { ussNextId :: !Int
    , ussModule :: !String
    }
    deriving (Show, Eq)

initialSupplyState :: String -> UniqueSupplyState
initialSupplyState moduleName =
    UniqueSupplyState
        { ussNextId = 0
        , ussModule = moduleName
        }

type UniqueSupply = State UniqueSupplyState

runUniqueSupply :: UniqueSupplyState -> UniqueSupply a -> (a, UniqueSupplyState)
runUniqueSupply st m = runState m st

evalUniqueSupply :: UniqueSupplyState -> UniqueSupply a -> a
evalUniqueSupply st m = evalState m st

execUniqueSupply :: UniqueSupplyState -> UniqueSupply a -> UniqueSupplyState
execUniqueSupply st m = execState m st

freshUnique :: String -> UniqueSupply Unique
freshUnique originalName = do
    st <- get
    let uid = ussNextId st
    let moduleName = ussModule st
    put st{ussNextId = uid + 1}
    pure
        Unique
            { uniqueId = uid
            , uniqueModule = moduleName
            , uniqueOriginal = originalName
            }

freshUniqueFrom :: Unique -> String -> UniqueSupply Unique
freshUniqueFrom base suffix = do
    st <- get
    let uid = ussNextId st
    put st{ussNextId = uid + 1}
    pure
        Unique
            { uniqueId = uid
            , uniqueModule = uniqueModule base
            , uniqueOriginal = uniqueOriginal base ++ "$" ++ suffix
            }
