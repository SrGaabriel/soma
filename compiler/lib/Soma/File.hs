module Soma.File where

import Data.HashMap.Strict qualified as HM
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Maple.Position (TreeId)
import System.FilePath (takeFileName)

type FileId = TreeId

data SourceFile = SourceFile
    { srcId :: !FileId
    , srcPath :: !FilePath
    , srcContent :: T.Text
    }
    deriving (Show, Eq)

srcName :: SourceFile -> String
srcName = takeFileName . srcPath

readSource :: FileId -> FilePath -> IO SourceFile
readSource fileId path = SourceFile fileId path <$> TIO.readFile path

newtype Files = Files (HM.HashMap FileId SourceFile)

mkFiles :: [SourceFile] -> Files
mkFiles srcs = Files (HM.fromList [(srcId src, src) | src <- srcs])

lookupFile :: Files -> FileId -> SourceFile
lookupFile (Files m) fileId =
    HM.findWithDefault (error ("lookupFile: unknown file " <> show fileId)) fileId m
