module Ide.Query.Database (
    Database,
    newDatabase,
    DatabaseSnapshot (..),
    snapshot,
    InputId,
    setInput,
    getInput,
    setInputWithDurability,
    QueryKey (..),
    QueryResult (..),
    query,
    queryMaybe,
    DependencyTracker,
    trackDependency,
    getDependencies,
    Cancellation,
    checkCancelled,
    cancel,
    DatabaseStats (..),
    getStats,
) where

import Control.Concurrent.STM
import Control.Exception (Exception, throwIO)
import Control.Monad (when)
import Data.Dynamic
import Data.HashMap.Strict qualified as HM
import Data.Hashable (Hashable (..))
import Data.IORef
import Data.Word (Word64)
import GHC.Generics (Generic)
import Ide.Query.Durability

newtype InputId = InputId {unInputId :: Word64}
    deriving (Eq, Ord, Show, Hashable)

data QueryKey = QueryKey
    { qkQueryType :: !String
    , qkArgs :: !Dynamic
    , qkHash :: {-# UNPACK #-} !Int
    }

instance Eq QueryKey where
    a == b = qkHash a == qkHash b && qkQueryType a == qkQueryType b

instance Hashable QueryKey where
    hashWithSalt s qk = hashWithSalt s (qkHash qk)

mkQueryKey :: (Typeable a, Hashable a) => String -> a -> QueryKey
mkQueryKey name args =
    QueryKey
        { qkQueryType = name
        , qkArgs = toDyn args
        , qkHash = hash (name, hash args)
        }

data QueryResult a = QueryResult
    { qrValue :: !a
    , qrRevision :: !Revision
    , qrDependencies :: ![InputId]
    , qrDurability :: !Durability
    }
    deriving (Show)

data CachedQuery = CachedQuery
    { cqValue :: !Dynamic
    , cqRevision :: !Revision
    , cqDependencies :: ![InputId]
    , cqDurability :: !Durability
    , cqVerifiedAt :: !Revision
    }

data StoredInput = StoredInput
    { siValue :: !Dynamic
    , siRevision :: !Revision
    , siDurability :: !Durability
    }

data Database = Database
    { dbInputs :: !(TVar (HM.HashMap InputId StoredInput))
    , dbQueries :: !(TVar (HM.HashMap QueryKey CachedQuery))
    , dbRevision :: !(TVar Revision)
    , dbNextInputId :: !(TVar Word64)
    , dbCancelled :: !(TVar Bool)
    , dbStats :: !(TVar DatabaseStats)
    }

data DatabaseStats = DatabaseStats
    { statsCacheHits :: !Word64
    , statsCacheMisses :: !Word64
    , statsRecomputations :: !Word64
    , statsInputChanges :: !Word64
    }
    deriving (Show, Eq, Generic)

initialStats :: DatabaseStats
initialStats = DatabaseStats 0 0 0 0

data DatabaseSnapshot = DatabaseSnapshot
    { dsInputs :: !(HM.HashMap InputId StoredInput)
    , dsQueries :: !(HM.HashMap QueryKey CachedQuery)
    , dsRevision :: !Revision
    }

data Cancellation = Cancellation
    deriving (Show)

instance Exception Cancellation

newDatabase :: IO Database
newDatabase =
    Database
        <$> newTVarIO HM.empty
        <*> newTVarIO HM.empty
        <*> newTVarIO initialRevision
        <*> newTVarIO 0
        <*> newTVarIO False
        <*> newTVarIO initialStats

snapshot :: Database -> IO DatabaseSnapshot
snapshot db = atomically $ do
    inputs <- readTVar (dbInputs db)
    queries <- readTVar (dbQueries db)
    rev <- readTVar (dbRevision db)
    return $ DatabaseSnapshot inputs queries rev

setInput :: (Typeable a) => Database -> a -> IO InputId
setInput db = setInputWithDurability db Medium

setInputWithDurability :: (Typeable a) => Database -> Durability -> a -> IO InputId
setInputWithDurability db durability value = atomically $ do
    inputId <- InputId <$> readTVar (dbNextInputId db)
    modifyTVar' (dbNextInputId db) (+ 1)

    rev <- nextRevision <$> readTVar (dbRevision db)
    writeTVar (dbRevision db) rev

    let stored =
            StoredInput
                { siValue = toDyn value
                , siRevision = rev
                , siDurability = durability
                }
    modifyTVar' (dbInputs db) (HM.insert inputId stored)

    modifyTVar' (dbStats db) (\s -> s{statsInputChanges = statsInputChanges s + 1})

    return inputId

getInput :: (Typeable a) => Database -> InputId -> IO (Maybe a)
getInput db inputId = do
    inputs <- readTVarIO (dbInputs db)
    return $ do
        stored <- HM.lookup inputId inputs
        fromDynamic (siValue stored)

newtype DependencyTracker = DependencyTracker (IORef [InputId])

trackDependency :: DependencyTracker -> InputId -> IO ()
trackDependency (DependencyTracker ref) inputId =
    modifyIORef' ref (inputId :)

getDependencies :: DependencyTracker -> IO [InputId]
getDependencies (DependencyTracker ref) = readIORef ref

query ::
    (Typeable a, Typeable r, Hashable a) =>
    Database ->
    String -> -- Query name
    a -> -- Query arguments
    (DependencyTracker -> a -> IO r) -> -- Query function
    IO r
query db name args compute = do
    checkCancelled db

    let key = mkQueryKey name args

    cached <- atomically $ do
        queries <- readTVar (dbQueries db)
        return $ HM.lookup key queries

    currentRev <- readTVarIO (dbRevision db)

    case cached of
        Just cq | isValid db cq currentRev -> do
            valid <- verifyDependencies db cq
            if valid
                then do
                    atomically
                        $ modifyTVar'
                            (dbStats db)
                            (\s -> s{statsCacheHits = statsCacheHits s + 1})
                    case fromDynamic (cqValue cq) of
                        Just v -> return v
                        Nothing -> recompute db key args compute
                else recompute db key args compute
        _ -> recompute db key args compute

queryMaybe ::
    (Typeable a, Typeable r, Hashable a) =>
    Database ->
    String ->
    a ->
    (DependencyTracker -> a -> IO (Maybe r)) ->
    IO (Maybe r)
queryMaybe db name args compute = do
    checkCancelled db
    query db name args compute

isValid :: Database -> CachedQuery -> Revision -> Bool
isValid _db cq currentRev =
    cqVerifiedAt cq == currentRev

verifyDependencies :: Database -> CachedQuery -> IO Bool
verifyDependencies db cq = do
    inputs <- readTVarIO (dbInputs db)
    return $ all (checkDep inputs) (cqDependencies cq)
  where
    checkDep inputs inputId =
        case HM.lookup inputId inputs of
            Nothing -> False
            Just stored -> siRevision stored <= cqRevision cq

recompute ::
    (Typeable r) =>
    Database ->
    QueryKey ->
    a ->
    (DependencyTracker -> a -> IO r) ->
    IO r
recompute db key args compute = do
    atomically
        $ modifyTVar'
            (dbStats db)
            ( \s ->
                s
                    { statsCacheMisses = statsCacheMisses s + 1
                    , statsRecomputations = statsRecomputations s + 1
                    }
            )

    tracker <- DependencyTracker <$> newIORef []

    result <- compute tracker args

    deps <- getDependencies tracker

    inputs <- readTVarIO (dbInputs db)
    let durability =
            minimum
                $ High
                    : [ siDurability s
                      | inputId <- deps
                      , Just s <- [HM.lookup inputId inputs]
                      ]

    currentRev <- readTVarIO (dbRevision db)
    let cached =
            CachedQuery
                { cqValue = toDyn result
                , cqRevision = currentRev
                , cqDependencies = deps
                , cqDurability = durability
                , cqVerifiedAt = currentRev
                }
    atomically $ modifyTVar' (dbQueries db) (HM.insert key cached)

    return result

checkCancelled :: Database -> IO ()
checkCancelled db = do
    cancelled <- readTVarIO (dbCancelled db)
    when cancelled $ throwIO Cancellation

cancel :: Database -> IO ()
cancel db = atomically $ writeTVar (dbCancelled db) True

getStats :: Database -> IO DatabaseStats
getStats db = readTVarIO (dbStats db)
