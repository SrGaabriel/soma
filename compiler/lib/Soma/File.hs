module Soma.File where

import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.FilePath (takeFileName)

data SourceFile = SourceFile
    { srcPath :: !FilePath
    , srcContent :: T.Text
    }
    deriving (Show, Eq)

srcName :: SourceFile -> String
srcName = takeFileName . srcPath

readSource :: FilePath -> IO SourceFile
readSource path = do
    content <- TIO.readFile path
    pure $ SourceFile path content
