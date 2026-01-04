module Ide.Vfs.FileSet (
    FileSet (unFileSet),
    newFileSet,
    addFile,
    updateFileContent,
    removeFileFromSet,
    getFileContent,
    getFileVersion,
    getAllFiles,
    getModifiedFiles,
    FileEntry (..),
    FileVersion,
    Workspace,
    newWorkspace,
    workspaceRoot,
    workspaceFiles,
    discoverFiles,
    isSourceFile,
) where

import Control.Concurrent.STM
import Data.HashMap.Strict qualified as HM
import Data.Text (Text)
import Data.Text.IO qualified as TIO
import Data.Time.Clock (UTCTime, getCurrentTime)
import Data.Word (Word64)
import Ide.Query.Queries (FileId, fileId)
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath (takeExtension, (</>))

type FileVersion = Word64

data FileEntry = FileEntry
    { feContent :: !Text
    , feVersion :: !FileVersion
    , feLastModified :: !UTCTime
    , feDirty :: !Bool
    }
    deriving (Show)

newtype FileSet = FileSet
    { unFileSet :: TVar (HM.HashMap FileId FileEntry)
    }

newFileSet :: IO FileSet
newFileSet = FileSet <$> newTVarIO HM.empty

addFile :: FileSet -> FileId -> Text -> IO FileVersion
addFile (FileSet fs) fid content = do
    now <- getCurrentTime
    atomically $ do
        files <- readTVar fs
        let version = case HM.lookup fid files of
                Just existing -> feVersion existing + 1
                Nothing -> 1
            entry =
                FileEntry
                    { feContent = content
                    , feVersion = version
                    , feLastModified = now
                    , feDirty = False
                    }
        writeTVar fs (HM.insert fid entry files)
        return version

updateFileContent :: FileSet -> FileId -> Text -> IO FileVersion
updateFileContent (FileSet fs) fid content = do
    now <- getCurrentTime
    atomically $ do
        files <- readTVar fs
        let version = case HM.lookup fid files of
                Just existing -> feVersion existing + 1
                Nothing -> 1
            entry =
                FileEntry
                    { feContent = content
                    , feVersion = version
                    , feLastModified = now
                    , feDirty = True
                    }
        writeTVar fs (HM.insert fid entry files)
        return version

removeFileFromSet :: FileSet -> FileId -> IO ()
removeFileFromSet (FileSet fs) fid =
    atomically
        $ modifyTVar' fs (HM.delete fid)

getFileContent :: FileSet -> FileId -> IO (Maybe Text)
getFileContent (FileSet fs) fid = do
    files <- readTVarIO fs
    return $ feContent <$> HM.lookup fid files

getFileVersion :: FileSet -> FileId -> IO (Maybe FileVersion)
getFileVersion (FileSet fs) fid = do
    files <- readTVarIO fs
    return $ feVersion <$> HM.lookup fid files

getAllFiles :: FileSet -> IO [FileId]
getAllFiles (FileSet fs) = HM.keys <$> readTVarIO fs

getModifiedFiles :: FileSet -> IO [FileId]
getModifiedFiles (FileSet fs) = do
    files <- readTVarIO fs
    return [fid | (fid, entry) <- HM.toList files, feDirty entry]

data Workspace = Workspace
    { wsRoot :: !FilePath
    , wsFiles :: !FileSet
    }

newWorkspace :: FilePath -> IO Workspace
newWorkspace root = Workspace root <$> newFileSet

workspaceRoot :: Workspace -> FilePath
workspaceRoot = wsRoot

workspaceFiles :: Workspace -> FileSet
workspaceFiles = wsFiles

isSourceFile :: FilePath -> Bool
isSourceFile path = takeExtension path == ".soma"

discoverFiles :: Workspace -> IO [FileId]
discoverFiles ws = do
    paths <- findSourceFiles (wsRoot ws)
    mapM (loadFile ws) paths

findSourceFiles :: FilePath -> IO [FilePath]
findSourceFiles dir = do
    exists <- doesDirectoryExist dir
    if not exists
        then return []
        else do
            entries <- listDirectory dir
            concat <$> mapM (processEntry dir) entries
  where
    processEntry base name = do
        let path = base </> name
        isDir <- doesDirectoryExist path
        if isDir
            then
                if name `elem` ["build", ".git", "node_modules", "target"]
                    then return []
                    else findSourceFiles path
            else
                if isSourceFile name
                    then return [path]
                    else return []

loadFile :: Workspace -> FilePath -> IO FileId
loadFile ws path = do
    content <- TIO.readFile path
    let fid = fileId path
    _ <- addFile (wsFiles ws) fid content
    return fid
