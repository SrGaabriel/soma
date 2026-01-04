module Souls.Logging where

import qualified Data.Text as T
import Data.Text.IO (hPutStrLn)
import System.IO (stderr)

logToClient :: String -> IO ()
logToClient msg = hPutStrLn stderr (T.pack $ "[Server Log] " ++ msg)
