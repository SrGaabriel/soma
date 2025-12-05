{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Metal.Unique (
    Unique (..),
    UniqueId,
    Name (..),
    UniqueSupply,
    newUniqueSupply,
    freshUnique,
    freshUniqueNamed,
    runUniqueSupply,
    evalUniqueSupply,
    nameToString,
    nameModule,
    isLocalName,
) where

import Control.Monad.State.Strict

type UniqueId = Int

data Unique = Unique
    { uniqueId :: !UniqueId
    , uniqueModule :: !String
    , uniqueOriginal :: !String
    }
    deriving (Show)

instance Eq Unique where
    u1 == u2 = uniqueId u1 == uniqueId u2 && uniqueModule u1 == uniqueModule u2

instance Ord Unique where
    compare u1 u2 =
        case compare (uniqueModule u1) (uniqueModule u2) of
            EQ -> compare (uniqueId u1) (uniqueId u2)
            other -> other

data Name
    = NUnique !Unique
    | NConstructor !String !String
    | NIntrinsic !String
    deriving (Show, Eq, Ord)

nameToString :: Name -> String
nameToString (NUnique u) =
    uniqueModule u <> "." <> uniqueOriginal u <> "$" <> show (uniqueId u)
nameToString (NConstructor modName ctorName) =
    modName <> "." <> ctorName
nameToString (NIntrinsic name) =
    name

nameModule :: Name -> Maybe String
nameModule (NUnique u) = Just (uniqueModule u)
nameModule (NConstructor modName _) = Just modName
nameModule (NIntrinsic _) = Nothing

isLocalName :: Name -> Bool
isLocalName (NUnique _) = True
isLocalName _ = False

data UniqueSupplyState = UniqueSupplyState
    { ussNextId :: !UniqueId
    , ussModule :: !String
    }

newtype UniqueSupply m a = UniqueSupply {unUniqueSupply :: StateT UniqueSupplyState m a}
    deriving (Functor, Applicative, Monad, MonadState UniqueSupplyState, MonadTrans)

newUniqueSupply :: String -> UniqueSupplyState
newUniqueSupply modName =
    UniqueSupplyState
        { ussNextId = 0
        , ussModule = modName
        }

freshUniqueNamed :: (Monad m) => String -> UniqueSupply m Unique
freshUniqueNamed originalName = do
    st <- get
    let uid = ussNextId st
        modName = ussModule st
    put st{ussNextId = uid + 1}
    pure
        Unique
            { uniqueId = uid
            , uniqueModule = modName
            , uniqueOriginal = originalName
            }

freshUnique :: (Monad m) => UniqueSupply m Unique
freshUnique = freshUniqueNamed "tmp"

runUniqueSupply :: String -> UniqueSupply m a -> m (a, UniqueSupplyState)
runUniqueSupply modName action =
    runStateT (unUniqueSupply action) (newUniqueSupply modName)

evalUniqueSupply :: (Monad m) => String -> UniqueSupply m a -> m a
evalUniqueSupply modName action =
    evalStateT (unUniqueSupply action) (newUniqueSupply modName)
